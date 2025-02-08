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

[%%prepare_logger]

module Xlist = Diffast_misc.Xlist
module Binding = Diffast_misc.Binding
module Astloc = Langs_common.Astloc
module Layeredloc = Langs_common.Layeredloc
module Ast_base = Langs_common.Ast_base

module Loc = Astloc
module LLoc = Layeredloc
module I = Pinfo
module B = Binding
module BID = Binding.ID
module L = Label
module N = Pinfo.Name
module NS = Pinfo.Name.Namespace
module NestedNS = Pinfo.Name.NestedNamespace
module Type = Pinfo.Type

open Common

let mk_macro_id i = "`"^i
let mk_macro_call_id ?(args="") i = sprintf "`%s(%s)" i args

let args_to_simple_string nl =
  String.concat "," (List.map (fun x -> L.to_simple_string x#label) nl)

let dummy_node_id = -1

[%%capture_path
class node
    ?(lloc=LLoc.dummy)
    ?(children=[])
    ?(info=I.NoInfo)
    ?(pvec=[])
    lab
    =
  object (self : 'self)
    val mutable encoded = ""
    val mutable parent = None
    val mutable lloc = lloc
    val mutable label = (lab : L.t)
    val mutable children = (children : 'self list)
    val mutable info = info
    val mutable binding = B.NoBinding
    val mutable pvec = pvec

    val mutable id_opt = None
    method id =
      match id_opt with
      | None -> begin
          let i = Oo.id self in
          id_opt <- Some i;
          i
      end
      | Some i -> i

    val mutable prefix = ""
    method add_prefix s = prefix <- s^prefix
    method get_prefix = prefix

    val mutable suffix = ""
    method add_suffix s = suffix <- suffix^s
    method get_suffix = suffix

    method set_parent p = parent <- Some p
    method parent : 'self =
      match parent with
      | Some p -> p
      | _ -> raise Not_found

    method iter_parents ?(upto=None) (f : 'self -> unit) =
      try
        let p = self#parent in
        let moveon =
          match upto with
          | Some x -> p != x
          | _ -> true
        in
        if moveon then begin
          f p;
          p#iter_parents ~upto f
        end
      with
        Not_found -> ()

    method encoded = encoded
    method set_encoded e =
      [%debug_log "%s" e];
      encoded <- e

    method pvec : int list =
      match children, pvec with
      | [], [] -> []
      | _, [] -> [self#nchildren]
      | _ -> pvec
    method set_pvec pv = pvec <- pv

    method nth_child n =
      [%debug_log "n=%d" n];
      try
        match n with
        | 0 -> List.hd children
        | _ -> List.nth children n
      with
        _ -> failwith (sprintf "Cpp.Ast.node#nth_child: %s" (L.to_string label))

    method nth_children n =
      [%debug_log "n=%d" n];
      let pv = self#pvec in
      match pv with
      | [] -> failwith (sprintf "Cpp.Ast.node#nth_children: %s" (L.to_string label))
      | [_] when n = 0 -> children
      | [_] -> failwith (sprintf "Cpp.Ast.node#nth_children: %s" (L.to_string label))
      | _ when n >= 0 -> begin
          let len =
            try
              List.nth pv n
            with _ -> failwith (sprintf "Cpp.Ast.node#nth_children: %s" (L.to_string label))
          in
          if len = 0 then
            []
          else
            try
              let _, f, t =
                List.fold_left
                  (fun (i, f, t) x ->
                    [%debug_log "  (%d,%d,%d) %d" i f t x];
                    if i < n then
                      (i+1, f+x, f+x)
                    else if i = n then
                      if x = 0 then
                        raise Not_found
                      else
                        (i+1, f, f+x-1)
                    else
                      (i, f, t)
                  ) (0, 0, 0) pv
              in
              [%debug_log "from=%d, to=%d" f t];
              let l = ref [] in
              try
                for i = f to t do
                  l := (List.nth children i) :: !l
                done;
                !l
              with
                _ -> invalid_arg (sprintf "Cpp.Ast.node#nth_children: %s" (L.to_string label))
            with
              Not_found -> []
      end
      | _ -> invalid_arg (sprintf "Cpp.Ast.node#nth_children: %s" (L.to_string label))

    method binding = binding
    method set_binding b = binding <- b

    method label = label
    method lloc = lloc
    method loc = lloc#get_loc
    method orig_loc = lloc#get_orig_loc
    method children = children
    method info = info

    method set_info i = info <- i

    method add_info i =
      match info with
      | I.NoInfo -> info <- i
      | _ -> info <- I.merge info i

    method children_labels =
      List.map (fun n -> n, n#label) children

    method nchildren = List.length children

    method set_lloc l = lloc <- l
    method set_children c = children <- c

    method relab lab = label <- lab

    method add_children_l c = children <- c @ children

    method add_children_r c = children <- children @ c

    method remove_rightmost_child =
      match children with
      | [] -> ()
      | [_] -> children <- []
      | _ ->
          match (List.rev children) with
          | _ :: t -> children <- (List.rev t)
          | _ -> assert false

    method remove_leftmost_child =
      match children with
      | [] -> ()
      | [_] -> children <- []
      | _ :: t -> children <- t

    method to_string =
      sprintf "<%s>%s%s%s"
        (L.to_string label)
        (lloc#to_string ?short:(Some true) ())
        (match info with
        | I.NoInfo -> ""
        | _ -> sprintf ": <<%s>>" (I.to_string info)
        )
        (match binding with
        | B.NoBinding -> ""
        | _ -> sprintf ": %a" BID.ps (B.get_bid binding)
        )

    method to_tag = L.to_tag label

    method get_name = L.get_name label

    method has_name = try let _ = self#get_name in true with _ -> false

    method get_name_opt = L.get_name_opt label

    method get_names = L.get_names label

    method get_label = L.get_label label

    method get_var = L.get_var label

    method get_var_opt = L.get_var_opt label


end (* of class Ast.node *)
]


let node_opt_to_name_opt = function
  | Some nd -> Some nd#get_name
  | None -> None

let node_list_to_name_list nds = Xlist.filter_map (fun n -> n#get_name_opt) nds


let lloc_of_locs loc0 loc1 =
  let lloc0 = LLoc.of_loc loc0 in
  let lloc1 = LLoc.of_loc loc1 in
  LLoc.merge lloc0 lloc1

let lloc_of_lexposs pos0 pos1 =
  let loc0 = Loc.of_lexpos pos0 in
  let loc1 = Loc.of_lexpos pos1 in
  lloc_of_locs loc0 loc1


[%%capture_path
let mknode (*env*)_ start_pos end_pos ?(info=I.NoInfo) ?(pvec=[]) label children =
  [%debug_log "%s (nchildren=%d)" (L.to_string label) (List.length children)];
  let lloc = lloc_of_lexposs start_pos end_pos in
  let nd = new node ~lloc ~children ~info ~pvec label in
  List.iter (fun x -> x#set_parent nd) children;
  nd
]

let mkleaf env start_pos end_pos ?(info=I.NoInfo) ?(pvec=[]) label =
  mknode env start_pos end_pos ~info ~pvec label []

[%%capture_path
let reloc (*env*)_ start_pos end_pos node =
  let lloc = lloc_of_lexposs start_pos end_pos in
  [%debug_log "relocating %s: %s -> %s"
    (L.to_string node#label)
    (node#lloc#to_string ?short:(Some true) ()) (lloc#to_string ?short:(Some true) ())];
  node#set_lloc lloc
]

[%%capture_path
let reloc_end (*env*)_ end_pos node =
  let lloc = lloc_of_lexposs end_pos end_pos in
  [%debug_log "relocating %s: %s -> %s"
    (L.to_string node#label)
    (node#lloc#to_string ?short:(Some true) ()) (lloc#to_string ?short:(Some true) ())];
  node#set_lloc (LLoc.merge node#lloc lloc)
]

(* *)

exception Node_found of node
exception Type_not_found

[%%capture_path
let find_node pred (nd : node) =
  let rec _find1 pred (nd : node) =
    [%debug_log "%s" (L.to_string nd#label)];
    if pred nd#label then
      raise (Node_found nd)
    else
      List.iter (_find1 pred) nd#children
  in
  try
    _find1 pred nd;
    raise Not_found
  with
    Node_found x -> x
]

let node_exists pred (nd : node) =
  try
    let _ = find_node pred nd in
    true
  with
    Not_found -> false

[%%capture_path
let find_nodes pred (nd : node) =
  let rec _find pred (nd : node) =
    [%debug_log "%s" (L.to_string nd#label)];
    let nl = List.concat_map (_find pred) nd#children in
    if pred nd#label then
      nd::nl
    else
      nl
  in
  _find pred nd
]

let int_pat = Str.regexp "^\\(-?\\)\\(0[bB][01']+\\|0[0-7']+\\|[0-9']+\\|0[xX][0-9a-fA-F']+\\)\\([uUlL]*\\)$"
let char_pat = Str.regexp "^\\(u8\\|[uUL@]\\)?'.+'$"
let str_pat = Str.regexp "^\\(u8\\|[uUL@]\\)?\".+\"$"

let get_char_ty_v pat s =
  if Str.string_match pat s 0 then begin
    let st = ref 1 in
    let len = ref ((String.length s) - 2) in
    let affix = try Str.matched_group 1 s with _ -> "" in
    let t =
      match affix with
      | "" -> "c"
      | "@" -> "c"
      | "u" -> incr st; decr len; "Ds"
      | "U" -> incr st; decr len; "Di"
      | "L" -> incr st; decr len; "w"
      | "u8" -> st := !st + 2; len := !len - 2; "Du"
      | _ -> [%warn_log "unknown affix: %s" affix]; "c"
    in
    t, String.sub s !st !len
  end
  else begin
    [%warn_log "unknown char pattern: %s" s];
    assert false
  end

let encode_ident = I.encode_ident
let decode_ident = I.decode_ident

[%%capture_path
let prefix_of_encoded s =
  [%debug_log "s=%s" s];
  if s = "" then
    s
  else
  let len = String.length s in
  let last_pos = ref 0 in
  let pos = ref 0 in
  let len_s = ref "" in
  let skipped = ref true in
  begin
    try
      while true do
        let c = s.[!pos] in
        let ci = Char.code c in
        if 48 <= ci && ci <= 57 then begin
          skipped := false;
          len_s := !len_s ^ (Char.escaped c);
          incr pos
        end
        else if !skipped then begin
          [%debug_log "skipped: %c" c];
          incr pos;
          if !pos >= len then
            raise Exit
        end
        else begin
          let i = int_of_string !len_s in
          [%debug_log "i=%d" i];
          len_s := "";
          pos := !pos + i;
          if !pos >= len then
            raise Exit
          else begin
            [%debug_log "last_pos: %d -> %d" !last_pos !pos];
            last_pos := !pos;
            skipped := true
          end
        end
      done
    with
      Exit -> ()
  end;
  if !last_pos = 0 then begin
    [%debug_log "s'=\"\""];
    ""
  end
  else begin
    let s' = String.sub s 0 !last_pos in
    [%debug_log "s'=%s" s'];
    s'
  end
]

[%%capture_path
let rec encode_name =
  let pat = Str.regexp "::" in
  let f name =
    let il = Str.split pat name in
    String.concat "" (List.map encode_ident il)
  in
  f

and encode_pointer_op : Type.pointer_op -> string = function
  | Star("", _) -> "P"
  | Star(n, _) -> sprintf "M%s" n
  | Amp -> "R"
  | AmpAmp -> "O"
  | Hat -> "U13block_pointer"
  | Macro i -> "U"^(encode_ident i)

and encode_type_ t = encode_type (Type.unwrap t)

and encode_type : Type.t -> string = function
  | SimpleTy sty -> Type.encode_simple_ty sty
  | ArrayTy(ty, dims) -> sprintf "A%d_%s" dims (encode_type ty)
  | PointerTy pty -> encode_pointer_ty pty
  | FunctionTy fty -> encode_function_ty fty
  | AltTy ts -> sprintf "(%s)" (list_to_string encode_type " | " ts)

and encode_pointer_ty {
  Type.pt_op=op;
  Type.pt_type=ty;
  Type.pt_qualifiers=q;
} =
  let q_str = q#to_string in
  let o_str = encode_pointer_op op in
  sprintf "%s%s%s" o_str q_str (encode_type ty)

and encode_function_ty {
  Type.ft_param_types=ptys;
  Type.ft_qualifiers=q;
  Type.ft_return_type=rty;
  Type.ft_is_vararg=_;
  Type.ft_params_macro=params_macro;
  Type.ft_virt_specs=_;
} =
  if params_macro = "" then
    sprintf "%s%sF%s%s%sE"
      q#encode_cv q#encode_exc
      (encode_type rty) (String.concat "" (List.map encode_type ptys))
      q#encode_ref
  else
    params_macro

and encode_expr (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  let encode_children code =
    sprintf "%s%s" code (String.concat "" (List.map encode_expr nd#children))
  in
  match nd#label with
  | IntegerLiteral i -> begin
      if Str.string_match int_pat i 0 then begin
        let st = ref 0 in
        let len = ref (String.length i) in
        let prefix =
          if (Str.matched_group 1 i) = "-" then begin
            st := 1;
            decr len;
            "n"
          end
          else
            ""
        in
        let suffix = String.lowercase_ascii (Str.matched_group 3 i) in
        let t =
          match suffix with
          | "" -> "i"
          | "l" -> decr len; "l"
          | "ll" -> len := !len - 2; "x"
          | "u" -> decr len; "j"
          | "ul" | "lu" -> len := !len - 2; "m"
          | "ull" | "llu" -> len := !len - 3; "y"
          | _ -> [%warn_log "unknown suffix: %s (%s)" suffix i]; "i"
        in
        let num = String.sub i !st !len in
        sprintf "L%s%s%s" t prefix num
      end
      else
        assert false
  end
  | FloatingLiteral f -> begin
      let len = String.length f in
      let t =
        match f.[len - 1] with
        | 'f' | 'F' -> "f"
        | 'l' | 'L' -> "e"
        | _ -> "d"
      in
      let rep =
        "<not yet>"
      in
      sprintf "L%s%sE" t rep
  end
  | CharacterLiteral c -> begin
      let t, v = get_char_ty_v char_pat c in
      sprintf "L%s%dE" t (Char.code v.[0])
  end
  | ConcatenatedString -> String.concat "" (List.map encode_string_literal nd#children)
  | BooleanLiteral b -> begin
      let e =
        match b with
        | "true" -> "1"
        | "false" -> "0"
        | _ -> assert false
      in
      sprintf "Lb%sE" e
  end
  | Nullptr -> "LDnE"
  | This -> "!!!This"
  | ParenthesizedExpression -> encode_expr (nd#nth_child 0)
  | Identifier i -> encode_ident i
  | PpConcatenatedIdentifier -> String.concat "##" (List.map encode_expr nd#children)
  | SimpleTemplateId i -> (encode_ident i)^(encode_template_arguments nd#children)
  | TypeId -> encode_type_id nd
  | OperatorFunctionId -> sprintf "on%s" (encode_op (nd#nth_child 0))
  | TemplateIdOp ->
      (encode_expr (nd#nth_child 0))^(encode_template_arguments (nd#nth_children 1))
  | LiteralOperatorId i -> sprintf "li%s" (encode_ident i)
  | TemplateIdLit ->
      (encode_expr (nd#nth_child 0))^(encode_template_arguments (nd#nth_children 1))
  | ConversionFunctionId -> "cv"^(encode_type_id (nd#nth_child 0))
  | Destructor -> begin
      let n0 = nd#nth_child 0 in
      let t =
        match n0#label with
        | DecltypeSpecifier -> (encode_decltype n0)
        | _ -> (encode_type_name n0)
      in
      "dn"^t
  end
  | QualifiedId -> (encode_nested_name_spec (nd#nth_child 0))^(encode_expr (nd#nth_child 1))

  | UnaryExpressionIncr -> "pp"^(encode_expr (nd#nth_child 0))
  | UnaryExpressionDecr -> "mm"^(encode_expr (nd#nth_child 0))
  | UnaryExpressionInd -> "de"^(encode_expr (nd#nth_child 0))
  | UnaryExpressionAddr -> "ad"^(encode_expr (nd#nth_child 0))
  | UnaryExpressionLabelAddr -> "la"^(encode_expr (nd#nth_child 0))
  | UnaryExpressionPlus -> "ps"^(encode_expr (nd#nth_child 0))
  | UnaryExpressionMinus -> "ng"^(encode_expr (nd#nth_child 0))
  | UnaryExpressionNeg _ -> "nt"^(encode_expr (nd#nth_child 0))
  | UnaryExpressionCompl _ -> "co"^(encode_expr (nd#nth_child 0))
  | UnaryExpressionSizeof -> begin
      match nd#children with
      | [n0] -> begin
          match n0#label with
          | TypeId -> sprintf "st%s" (encode_type_id n0)
          | _ -> sprintf "sz%s" (encode_expr n0)
      end
      | _ -> assert false
  end
  | UnaryExpressionSizeofPack _ -> "!!!UnaryExpressionSizeofPack"
  | UnaryExpressionAlignof -> ""^(encode_expr (nd#nth_child 0))
  | NoexceptExpression -> "nx"^(encode_expr (nd#nth_child 0))
  | NewExpression -> begin
      let prefix =
        if node_exists (function L.NoptrNewDeclarator -> true | _ -> false) nd then
          "na"
        else
          "nw"
      in
      let gs =
        match nd#nth_children 0 with
        | [_] -> "gs"
        | _ -> ""
      in
      let e =
        match nd#nth_children 1 with
        | [] -> ""
        | [n0] -> String.concat "" (List.map encode_expr n0#children)
        | _ -> assert false
      in
      let t =
        match nd#nth_children 2 with
        | [n0] -> begin
            match n0#label with
            | TypeId -> encode_type_id n0
            | _ -> encode_type_id n0
        end
        | _ -> assert false
      in
      let ini =
        match nd#nth_children 3 with
        | [] -> "E"
        | [n0] -> begin
            match n0#label with
            | NewInitializer ->
                sprintf "pi%sE" (String.concat "" (List.map encode_expr n0#children))
            | _ -> "E" (* ??? *)
        end
        | _ -> assert false
      in
      sprintf "%s%s%s_%s%s" gs prefix e t ini
  end
  | DeleteExpression -> begin
      let gs =
        match nd#nth_children 0 with
        | [_] -> "gs"
        | _ -> ""
      in
      let e =
        match nd#nth_children 1 with
        | [n0] -> encode_expr n0
        | _ -> assert false
      in
      sprintf "%sdl%s" gs e
  end
  | DeleteExpressionBracket -> begin
      let gs =
        match nd#nth_children 0 with
        | [_] -> "gs"
        | _ -> ""
      in
      let e =
        match nd#nth_children 1 with
        | [n0] -> encode_expr n0
        | _ -> assert false
      in
      sprintf "%sda%s" gs e
  end
  | PostfixExpressionSubscr -> encode_children "ix"
  | PostfixExpressionFunCall -> (encode_children "cl")^"E"
  | PostfixExpressionExplicitTypeConvExpr -> begin
      let e0 = encode_type (simple_type_of_decl_spec_seq (nd#nth_children 0)) in
      match nd#children with
      | [_] -> sprintf "cv%s_E" e0
      | [_; n1] -> sprintf "cv%s%s" e0 (encode_expr n1)
      | _ :: rest -> sprintf "cv%s_%sE" e0 (String.concat "" (List.map encode_expr rest))
      | [] -> assert false
  end
  | PostfixExpressionExplicitTypeConvBraced -> begin
      let e0 = encode_type (simple_type_of_decl_spec_seq (nd#nth_children 0)) in
      sprintf "tl%s%s" e0 (String.concat "" (List.map encode_expr (nd#nth_child 1)#children))
  end
  | PostfixExpressionDot -> begin
      let nm =
        match nd#nth_children 2 with
        | [n2] -> encode_expr n2
        | _ -> assert false
      in
      "dt"^(encode_expr (nd#nth_child 0))^nm
  end
  | PostfixExpressionArrow -> begin
      let nm =
        match nd#nth_children 2 with
        | [n2] -> encode_expr n2
        | _ -> assert false
      in
      "pt"^(encode_expr (nd#nth_child 0))^nm
  end
  | PostfixExpressionIncr -> "pp_"^(encode_expr (nd#nth_child 0))
  | PostfixExpressionDecr -> "mm_"^(encode_expr (nd#nth_child 0))
  | PostfixExpressionDynamic_cast -> begin
      let t = encode_type_id (nd#nth_child 0) in
      sprintf "dc%s%s" t (encode_expr (nd#nth_child 1))
  end
  | PostfixExpressionStatic_cast -> begin
      let t = encode_type_id (nd#nth_child 0) in
      sprintf "sc%s%s" t (encode_expr (nd#nth_child 1))
  end
  | PostfixExpressionReinterpret_cast -> begin
      let t = encode_type_id (nd#nth_child 0) in
      sprintf "rc%s%s" t (encode_expr (nd#nth_child 1))
  end
  | PostfixExpressionConst_cast -> begin
      let t = encode_type_id (nd#nth_child 0) in
      sprintf "cc%s%s" t (encode_expr (nd#nth_child 1))
  end
  | PostfixExpressionTypeidExpr -> sprintf "te%s" (encode_expr (nd#nth_child 0))
  | PostfixExpressionTypeidTy ->
      sprintf "ti%s" (encode_type_id (nd#nth_child 0))

  | BracedInitList -> sprintf "il%sE" (String.concat "" (List.map encode_expr nd#children))
  | DesignatedInitializerClause -> begin
      let i =
        match (nd#nth_child 0)#label with
        | DesignatorField i -> i
        | _ -> assert false
      in
      sprintf "di%s%s" (encode_ident i) (encode_expr (nd#nth_child 1))
  end
  | TypenameSpecifier i -> begin
      match nd#nth_children 0, nd#nth_children 1 with
      | [], [] -> encode_ident i
      | [], [s] -> encode_expr s
      | [n], [] -> sprintf "N%s%sE" (encode_nested_name_spec n) (encode_ident i)
      | [n], [s] -> sprintf "N%s%sE" (encode_nested_name_spec n) (encode_expr s)
      | _ -> assert false
  end
  | CastExpression                 -> encode_children "cv"
  | PmExpressionClass              -> encode_children "ds"
  | PmExpressionPtr                -> encode_children "pm"
  | MultiplicativeExpressionMult   -> encode_children "ml"
  | MultiplicativeExpressionDiv    -> encode_children "dv"
  | MultiplicativeExpressionMod    -> encode_children "rm"
  | AdditiveExpressionAdd          -> encode_children "pl"
  | AdditiveExpressionSubt         -> encode_children "mi"
  | ShiftExpressionLeft            -> encode_children "ls"
  | ShiftExpressionRight           -> encode_children "rs"
  | CompareExpression              -> encode_children "ss"
  | RelationalExpressionLt         -> encode_children "lt"
  | RelationalExpressionGt         -> encode_children "gt"
  | RelationalExpressionLe         -> encode_children "le"
  | RelationalExpressionGe         -> encode_children "ge"
  | EqualityExpressionEq           -> encode_children "eq"
  | EqualityExpressionNeq _        -> encode_children "ne"
  | AndExpression _                -> encode_children "an"
  | ExclusiveOrExpression _        -> encode_children "eo"
  | InclusiveOrExpression _        -> encode_children "or"
  | LogicalAndExpression _         -> encode_children "aa"
  | LogicalOrExpression _          -> encode_children "oo"
  | ConditionalExpression          -> encode_children "qu"
  | AssignmentExpressionEq         -> encode_children "aS"
  | AssignmentExpressionPlus       -> encode_children "pL"
  | AssignmentExpressionMinus      -> encode_children "mI"
  | AssignmentExpressionMult       -> encode_children "mL"
  | AssignmentExpressionDiv        -> encode_children "dV"
  | AssignmentExpressionMod        -> encode_children "rM"
  | AssignmentExpressionShiftLeft  -> encode_children "lS"
  | AssignmentExpressionShiftRight -> encode_children "rS"
  | AssignmentExpressionAnd _      -> encode_children "aN"
  | AssignmentExpressionXor _      -> encode_children "eO"
  | AssignmentExpressionOr _       -> encode_children "oR"


  | x -> sprintf "!!!%s" (L.to_string x)

and encode_type_id (nd : node) = encode_type (type_of_type_id nd)

and encode_nested_name_spec (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | NestedNameSpecifierHead -> "gs"
  | NestedNameSpecifierIdent uqn -> begin
      match nd#nth_children 0 with
      | [] -> uqn
      | [n0] -> (encode_nested_name_spec n0)^uqn
      | _ -> assert false
  end
  | NestedNameSpecifierTempl uqn -> begin
      match nd#nth_children 0 with
      | [] -> uqn
      | [n0] -> (encode_nested_name_spec n0)^uqn
      | _ -> assert false
  end
  | NestedNameSpecifierDeclty -> encode_decltype (nd#nth_child 0)
  | _ -> invalid_arg "Cpp.Ast.encode_nested_name_spec"

and encode_decltype (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | DecltypeSpecifier -> begin
      let n0 = nd#nth_child 0 in
      let prefix =
        match n0#label with
        | Identifier _ | OperatorFunctionId | ConversionFunctionId | LiteralOperatorId _
        | Destructor | SimpleTemplateId _ | TemplateIdOp | TemplateIdLit
        | IdentifierMacroInvocation _ | PostfixExpressionDot | PostfixExpressionArrow -> "Dt"
        | _ -> "DT"
      in
      sprintf "%s%sE" prefix (encode_expr n0)
  end
  | _ -> invalid_arg "Cpp.Ast.encode_decltype"

and encode_type_name (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | TypeName i -> encode_ident i
  | _ -> encode_expr nd

and encode_op ?(unary=false) (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | Plus when unary       -> "ps"
  | Minus when unary      -> "ng"
  | Amp _ when unary      -> "ad"
  | Star when unary       -> "de"
(*  | PlusPlus when unary   -> "pp"
  | MinusMinus when unary -> "mm"*)
  | New                   -> "nw"
  | Delete                -> "dl"
  | NewBracket            -> "na"
  | DeleteBracket         -> "da"
  | Parentheses           -> "cl"
  | Brackets              -> "ix"
  | MinusGt               -> "pt"
  | MinusGtStar           -> "pm"
  | Tilde _               -> "co"
  | Exclam _              -> "nt"
  | Plus                  -> "pl"
  | Minus                 -> "mi"
  | Star                  -> "ml"
  | Slash                 -> "dv"
  | Perc                  -> "rm"
  | Hat _                 -> "eo"
  | Amp _                 -> "an"
  | Bar _                 -> "or"
  | Eq                    -> "aS"
  | PlusEq                -> "pL"
  | MinusEq               -> "mI"
  | StarEq                -> "mL"
  | SlashEq               -> "dV"
  | PercEq                -> "rM"
  | HatEq _               -> "eO"
  | AmpEq _               -> "aN"
  | BarEq _               -> "oR"
  | EqEq                  -> "eq"
  | ExclamEq _            -> "ne"
  | Lt                    -> "lt"
  | Gt                    -> "gt"
  | LtEq                  -> "le"
  | GtEq                  -> "ge"
  | LtEqGt                -> "ss"
  | AmpAmp _              -> "aa"
  | BarBar _              -> "oo"
  | LtLt                  -> "ls"
  | GtGt                  -> "rs"
  | LtLtEq                -> "lS"
  | GtGtEq                -> "rS"
  | PlusPlus              -> "pp"
  | MinusMinus            -> "mm"
  | Comma                 -> "cm"
  | OperatorMacro i       -> "v"^(encode_ident i)
  | _ -> invalid_arg "Cpp.Ast.encode_op"

and encode_template_arguments (nds : node list) =
  let el =
    List.map
      (fun x ->
        match x#label with
        | L.PackExpansion -> sprintf "J%sE" (String.concat "" (List.map encode_expr nds))
        | _ -> begin
            let e = encode_expr x in
            if e.[0] = 'L' then
              e
            else
              sprintf "X%sE" e
        end
      ) nds
  in
  sprintf "I%sE" (String.concat "" el)

and encode_string_literal (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | StringLiteral s -> begin
      let ty, _ = get_char_ty_v str_pat s in
      sprintf "LA%d_K%sE" (String.length s) ty
  end
  | StringMacro _ | PpStringized _ -> ""
  | _ -> invalid_arg "Cpp.Ast.encode_string_literal"

and uqn_of_ident_macro_invocation (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | IdentifierMacroInvocation i ->
      let args = args_to_simple_string nd#children in
      mk_macro_call_id ~args i
  | _ -> invalid_arg "Cpp.Ast.uqn_of_ident_macro_invocation"

and uqn_of_simple_template_id (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | SimpleTemplateId i -> (encode_ident i)^(encode_template_arguments nd#children)
  | SimpleTemplateIdM ->
      (uqn_of_ident_macro_invocation (nd#nth_child 0))^
      (encode_template_arguments (nd#nth_children 1))
  | IdentifierMacroInvocation _ -> uqn_of_ident_macro_invocation nd
  | _ -> invalid_arg "Cpp.Ast.uqn_of_simple_template_id"

and qn_of_elaborated_type_specifier (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | ElaboratedTypeSpecifierClass uqn
  | ElaboratedTypeSpecifierStruct uqn
  | ElaboratedTypeSpecifierUnion uqn -> begin
      match nd#nth_children 1 with
      | [] -> uqn
      | [n] -> (encode_nested_name_spec n)^uqn
      | _ -> assert false
  end
  | ElaboratedTypeSpecifierEnum uqn -> begin
      match nd#children with
      | [] -> uqn
      | [n] -> (encode_nested_name_spec n)^uqn
      | _ -> assert false
  end
  | _ -> invalid_arg "Cpp.Ast.qn_of_elaborated_type_specifier"

and qn_of_simple_type_specifier (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | SimpleTypeSpecifier uqn -> begin
      match nd#nth_children 0 with
      | [] -> uqn
      | [n] -> (encode_nested_name_spec n)^uqn
      | _ -> assert false
  end
  | DecltypeSpecifier -> encode_decltype nd
  | PlaceholderTypeSpecifierAuto | PlaceholderTypeSpecifierDecltype
  | Char | Char8_t | Char16_t | Char32_t | Wchar_t | Bool | Short | Int | Long
  | Signed | Unsigned | Float | Double | Void -> raise Not_found
  | _ -> invalid_arg "Cpp.Ast.qn_of_simple_type_specifier"

and qn_of_typename_specifier (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | TypenameSpecifier uqn -> begin
      match nd#nth_children 0 with
      | [] -> uqn
      | [n] -> (encode_nested_name_spec n)^uqn
      | _ -> [%debug_log "@"]; assert false
  end
  | _ -> invalid_arg "Cpp.Ast.qn_of_typename_specifier"

and uqn_of_type_name (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | TypeName i -> encode_ident i
  | _ -> uqn_of_simple_template_id nd

and uqn_of_unqualified_id (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | Identifier i -> encode_ident i
  | SimpleTemplateId _ | SimpleTemplateIdM -> uqn_of_simple_template_id nd
  | Destructor -> begin
      let c = nd#nth_child 0 in
      match c#label with
      | TypeName _ | SimpleTemplateId _ -> "D"^(uqn_of_type_name c) (* ! *)
      | DecltypeSpecifier -> "D"^(encode_decltype c) (* ! *)
      | IdentifierMacroInvocation _ -> "D"^(uqn_of_ident_macro_invocation c) (* ! *)
      | lab ->
          let _ = lab in
          [%debug_log "%s" (L.to_string lab)];
          assert false
  end
  | IdentifierMacroInvocation _ -> uqn_of_ident_macro_invocation nd
  | OperatorFunctionId
  | ConversionFunctionId
  | LiteralOperatorId _
  | TemplateIdOp
  | TemplateIdLit
  | PpConcatenatedIdentifier
    -> encode_expr nd
  | _ -> invalid_arg "Cpp.Ast.uqn_of_unqualified_id"

and uqn_of_conversion_function_id (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | ConversionFunctionId -> encode_expr nd
  | _ -> invalid_arg "Cpp.Ast.uqn_of_conversion_function_id"

and uqn_of_operator_function_id (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | OperatorFunctionId -> encode_expr nd
  | _ -> invalid_arg "Cpp.Ast.uqn_of_operator_function_id"

and uqn_of_literal_operator_id (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | LiteralOperatorId _ -> encode_expr nd
  | _ -> invalid_arg "Cpp.Ast.uqn_of_literal_operator_id"

and uqn_of_template_id (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | TemplateIdOp
  | TemplateIdLit -> encode_expr (nd#nth_child 0)
  | _ -> uqn_of_simple_template_id nd

and type_spec_list_of_node_list ?(ns="") (nds : node list) =
  match nds with
  | [nd] when begin
      match nd#label with
      | TypeSpecifierSeq -> true
      | _ -> false
  end -> List.map (type_spec_of_node ~ns) (nd#nth_children 0)
  | _ -> List.map (type_spec_of_node ~ns) nds

and qn_of_class_or_decltype (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | QualifiedTypeName -> begin
      let prefix = encode_nested_name_spec (nd#nth_child 0) in
      let uqn = uqn_of_type_name (nd#nth_child 1) in
      prefix^uqn
  end
  | DecltypeSpecifier -> encode_decltype nd
  | _ -> uqn_of_type_name nd

and uqn_of_class_name (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | ClassName uqn -> uqn
  | _ -> invalid_arg "Cpp.Ast.uqn_of_class_name"

and qn_of_class_head_name (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | ClassHeadName qn -> qn
  | IdentifierMacroInvocation i -> begin
    let args = args_to_simple_string nd#children in
    (mk_macro_call_id ~args i)
  end
  | _ -> uqn_of_class_name nd

and qn_of_enum_head_name (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | EnumHeadName uqn -> begin
      match nd#nth_children 0 with
      | [] -> uqn
      | [n] -> begin
          let p = encode_nested_name_spec n in
          p^uqn
      end
      | _ -> assert false
  end
  | _ -> invalid_arg "Cpp.Ast.qn_of_enum_head_name"

and qn_list_of_using_declaration (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | UsingDeclaration -> List.map qn_of_using_declarator nd#children
  | _ -> invalid_arg "Cpp.Ast.qn_list_of_using_declaration"

and qn_of_using_declarator (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | UsingDeclarator -> begin
      match nd#nth_children 1 with
      | [n] -> begin
          let p = encode_nested_name_spec n in
          match nd#nth_children 2 with
          | [n] -> p, uqn_of_unqualified_id n
          | _ -> assert false
      end
      | _ -> assert false
  end
  | PackExpansion -> qn_of_using_declarator (nd#nth_child 0)
  | _ -> invalid_arg "Cpp.Ast.qn_of_using_declarator"

and qn_list_of_using_enum_declaration (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | UsingEnumDeclaration -> List.map qn_of_using_enum_declarator nd#children
  | _ -> invalid_arg "Cpp.Ast.qn_list_of_using_enum_declaration"

and qn_of_using_enum_declarator (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | UsingEnumDeclarator -> begin
      match nd#nth_children 0 with
      | [] -> begin
          match nd#nth_children 1 with
          | [n] -> "", uqn_of_unqualified_id n
          | _ -> assert false
      end
      | [n] -> begin
          let p = encode_nested_name_spec n in
          match nd#nth_children 1 with
          | [n] -> p, uqn_of_unqualified_id n
          | _ -> assert false
      end
      | _ -> assert false
  end
  | PackExpansion -> qn_of_using_enum_declarator (nd#nth_child 0)
  | _ -> invalid_arg "Cpp.Ast.qn_of_using_enum_declarator"

and qn_of_qualified_id (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | QualifiedId -> begin
      try
        let prefix = encode_nested_name_spec (nd#nth_child 0) in
        prefix^(uqn_of_unqualified_id (nd#nth_child 1))
      with
        Failure _ -> assert false
  end
  | _ -> invalid_arg "Cpp.Ast.qn_of_qualified_id"

and qn_of_id_expression (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | QualifiedId -> qn_of_qualified_id nd
  | _ -> uqn_of_unqualified_id nd

and qn_of_declarator_id (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | PackExpansion -> begin
      try
        "..."^(qn_of_id_expression (nd#nth_child 0))
      with
        Failure _ -> assert false
  end
  | _ -> qn_of_id_expression nd

and qualifiers_of_node_list (nds : node list) =
  let q = new I.qualifiers in
  List.iter
    (fun (nd : node) ->
      match nd#label with
      | Const -> q#set_const()
      | Volatile -> q#set_volatile()
      | RefQualifierAmp -> q#set_amp()
      | RefQualifierAmpAmp -> q#set_amp_amp()
      | NoexceptSpecifier when nd#children <> [] -> begin
          match nd#children with
          | [n] -> q#set_noexcept_computed (encode_expr n)
          | _ -> assert false
      end
      | NoexceptSpecifier -> q#set_noexcept()
      | NoexceptSpecifierThrow -> q#set_throw()
      | Restrict _ -> q#set_restrict()
      | MsStdcall _ -> q#set_stdcall()
      | MsCdecl _ -> q#set_cdecl()
      | _ -> ()
    ) nds;
  q

and virt_specs_of_node_list (nds : node list) =
  let v = new I.virt_specs in
  List.iter
    (fun (nd : node) ->
      match nd#label with
      | VirtSpecifierFinal -> v#set_final()
      | VirtSpecifierOverride -> v#set_override()
      | ClassVirtSpecifierFinal -> v#set_final()
      | _ -> ()
    ) nds;
  v

and nested_namespace_of_node (nd : node) =
  match nd#label with
  | EnclosingNamespaceSpecifier i -> begin
      match nd#children with
      | [] -> NestedNS.mk1 (NS.mk i)
      | [nd0] -> NestedNS.append (nested_namespace_of_node nd0) (NS.mk i)
      | [nd0; _] -> NestedNS.append (nested_namespace_of_node nd0) (NS.mk ~inline:true i)
      | _ -> assert false
  end
  | _ -> invalid_arg "Cpp.Ast.nested_namespace_of_node"

and access_spec_of_node (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | Private   -> N.Spec.Aprivate
  | Protected -> N.Spec.Aprotected
  | Public    -> N.Spec.Apublic
  | AccessSpecMacro i -> N.Spec.Amacro i
  | _  -> invalid_arg "Cpp.Ast.access_spec_of_node"

and base_spec_of_node ns (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | BaseSpecifier -> begin
      let access_spec =
        match (nd#nth_children 1) @ (nd#nth_children 3) with
        | [] -> None
        | [a] -> Some (access_spec_of_node a)
        | _ -> assert false
      in
      let is_virtual =
        match nd#nth_children 2 with
        | [] -> false
        | [_] -> true
        | _ -> assert false
      in
      let ident =
        match nd#nth_children 4 with
        | [c] -> ns^(qn_of_class_or_decltype c)
        | _ -> assert false
      in
      let spec = new N.Spec.base_spec ~access_spec ~is_virtual ident in
      spec
  end
  | PackExpansion -> begin
      let spec = base_spec_of_node ns (nd#nth_child 0) in
      spec#set_is_pack_expansion();
      spec
  end
  | BaseSpecMacro i -> begin
      new N.Spec.base_spec (mk_macro_id i)
  end
  | BaseSpecMacroInvocation i -> begin
      new N.Spec.base_spec (mk_macro_call_id i)
  end
  | _ -> invalid_arg "Cpp.Ast.base_spec_of_node"

and alt_base_specs_list_of_node ns (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | PpIfSection _ -> begin
      let ifg =
        try
          [fst (base_specs_of_base_clause ns ((nd#nth_child 0)#nth_child 1))]
        with _ -> []
      in
      let elifg =
        try
          List.map
            (fun x -> fst (base_specs_of_base_clause ns (x#nth_child 1))) (nd#nth_children 1)
        with _ -> []
      in
      let elsg =
        try
          List.map
            (fun x -> fst (base_specs_of_base_clause ns (x#nth_child 1))) (nd#nth_children 2)
        with _ -> []
      in
      ifg @ elifg @ elsg
  end
  | _ -> invalid_arg "Cpp.Ast.alt_base_specs_list_of_node"

and base_specs_of_base_clause ns (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | BaseClause -> begin
      List.fold_left
        (fun (bss, abssl) x ->
          match x#label with
          | L.PpIfSection _ -> begin
              let alt_base_specs_list = alt_base_specs_list_of_node ns x in
              match alt_base_specs_list with
              | [] -> bss, abssl
              | ys::yss ->
                  ys @ bss,
                  List.concat_map (fun abss -> List.map (fun ys -> ys @ abss) yss) abssl
          end
          | _ -> bss @ [(base_spec_of_node ns x)], abssl
        ) ([], []) nd#children
  end
  | ClassVirtSpecifierFinal
  | ClassVirtSpecifierMsSealed
  | VirtSpecifierMacro _ -> [], []
  | L.PpIfSection _ -> begin
      let alt_base_specs_list = alt_base_specs_list_of_node ns nd in
      match alt_base_specs_list with
      | [] -> [], []
      | ys::_ -> ys, []
  end
  | _ -> invalid_arg "Cpp.Ast.base_specs_of_base_clause"

and qn_class_spec_of_class ns (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | ClassHeadClass | ClassHeadStruct | ClassHeadUnion | ClassHeadMsRefClass -> begin
      let qn =
        match nd#nth_children 1 with
        | [] -> ""
        | [n] -> qn_of_class_head_name n
        | _ -> assert false
      in
      let base_specs, alt_base_specs_list =
        match nd#nth_children 3 with
        | [] -> [], []
        | [b] -> base_specs_of_base_clause ns b
        | _ -> assert false
      in
      let spec = new N.Spec.class_spec ~base_specs ~alt_base_specs_list qn in
      begin
        match nd#nth_children 2 with
        | [v] -> begin
            match v#label with
            | ClassVirtSpecifierFinal -> spec#virt_specs#set_final()
            | ClassVirtSpecifierMsSealed -> spec#virt_specs#set_final()
            | VirtSpecifierMacro _ -> ()
            | _ -> assert false
        end
        | _ -> ()
      end;
      qn, spec
  end
  | ClassHeadMacroInvocation i -> begin
      let qn =
        match nd#nth_children 1 with
        | [] -> mk_macro_call_id i
        | [n] -> qn_of_class_head_name n
        | _ -> assert false
      in
      let spec = new N.Spec.class_spec qn in
      qn, spec
  end
  | ClassHeadMacro i -> begin
      let qn = mk_macro_id i in
      let spec = new N.Spec.class_spec qn in
      qn, spec
  end
  | _ -> invalid_arg "Cpp.Ast.qn_class_spec_of_class"

and qn_enum_spec_of_enum ns (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | EnumHeadEnum | EnumHeadEnumClass | EnumHeadEnumStruct
  | OpaqueEnumDeclaration
  | OpaqueEnumDeclarationClass
  | OpaqueEnumDeclarationStruct -> begin
      let qn =
        match nd#nth_children 1 with
        | [] -> ""
        | [n] -> qn_of_enum_head_name n
        | _ -> assert false
      in
      let enum_base =
        match nd#nth_children 2 with
        | [] -> None
        | [b] -> Some (enum_base_of_node ns b)
        | _ -> assert false
      in
      let spec = new N.Spec.enum_spec ~enum_base qn in
      qn, spec
  end
  | EnumHeadEnumMacro i | OpaqueEnumDeclarationMacro i when begin
      i = "NS_ENUM" ||
      i = "NS_OPTIONS"
  end -> begin
    let qn = (nd#nth_child 1)#get_name in
    let spec = new N.Spec.enum_spec qn in
    qn, spec
  end
  | _ -> invalid_arg "Cpp.Ast.qn_enum_spec_of_enum"

and ident_type_param_spec_of_type_param (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | TypeParameter i -> begin
      match nd#nth_children 2 with
      | [n] -> begin
          match n#label with
          | TypeParameterKeyClass    -> i, N.Spec.Pclass
          | TypeParameterKeyTypename -> i, N.Spec.Ptypename
          | PackExpansion -> begin
              match (n#nth_child 0)#label with
              | TypeParameterKeyClass    -> i, N.Spec.PclassPack
              | TypeParameterKeyTypename -> i, N.Spec.PtypenamePack
              | _ -> assert false
          end
          | _ -> assert false
      end
      | _ -> begin
          match nd#nth_children 0 with
          | [n] -> begin
              match n#label with
              | TypeConstraint uqn -> begin
                  let p =
                    match n#nth_children 0 with
                    | [n] -> encode_nested_name_spec n
                    | _ -> ""
                  in
                  i, N.Spec.Pconcept(p, uqn)
              end
              | PackExpansion -> begin
                  let n0 = n#nth_child 0 in
                  match n0#label with
                  | TypeConstraint uqn -> begin
                      let p =
                        match n0#nth_children 0 with
                        | [n] -> encode_nested_name_spec n
                        | _ -> ""
                      in
                      i, N.Spec.Pconcept(p, uqn)
                  end
                  | _ -> assert false
              end
              | _ -> assert false
          end
          | _ -> assert false
      end
  end
  | _ -> invalid_arg "Cpp.Ast.ident_type_param_spec_of_type_param"

and pointer_op_of_node (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | PtrOperatorStar -> begin
      let prefix =
        match nd#nth_children 0 with
        | [] -> ""
        | [n] -> encode_nested_name_spec n
        | _ -> assert false
      in
      let q = qualifiers_of_node_list (nd#nth_children 2) in
      Type.Star(prefix, q)
  end
  | PtrOperatorAmp -> Type.Amp
  | PtrOperatorAmpAmp -> Type.AmpAmp
  | PtrOperatorHat -> Type.Hat
  | PtrMacro i -> Type.Macro i
  | _ -> invalid_arg "Cpp.Ast.pointer_op_of_node"

and qn_type_list_of_simple_decl (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | SimpleDeclaration -> begin
      let sty = simple_type_of_decl_spec_seq (nd#nth_children 1) in
      [%debug_log "sty=%s" (Type.to_string sty)];
      match nd#nth_children 2 with
      | [] -> begin
          match Type.idents_of_simple_type sty with
          | [i] -> [nd, i, sty] (* typedef? *)
          | _ -> []
      end
      | l -> begin
          List.filter_map
            (fun x ->
              match x#label with
              | L.InitDeclarator _ | PpIfSection _ -> begin
                  let i, w = qn_wrap_of_init_declarator x in
                  Some (x, i, w sty)
              end
              | _ -> None
            ) l
      end
  end
  | PpIfSection _ -> begin
      let if_itl = try qn_type_list_of_simple_decl ((nd#nth_child 0)#nth_child 1) with _ -> [] in
      let elif_itl =
        List.flatten
          (Xlist.filter_map
             (fun x -> try Some (qn_type_list_of_simple_decl (x#nth_child 1)) with _ -> None)
             (nd#nth_children 1))
      in
      let else_itl =
        List.flatten
          (Xlist.filter_map
             (fun x -> try Some (qn_type_list_of_simple_decl (x#nth_child 1)) with _ -> None)
             (nd#nth_children 2))
      in
      if_itl @ elif_itl @ else_itl
  end
  | DeclarationMacro _ -> []
  | _ -> invalid_arg "Cpp.Ast.qn_type_list_of_simple_decl"

and qn_type_list_of_enumerator scope (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  let rec get_qn (n : node) =
    match n#label with
    | Enumerator i -> encode_ident i
    | EnumeratorMacroInvocation i -> mk_macro_call_id i
    | EnumeratorDefinition -> get_qn (n#nth_child 0)
    | EnumeratorDefinitionMacro i -> mk_macro_id i
    | _ -> invalid_arg "Cpp.Ast.qn_type_list_of_enumerator"
  in
  let qn = get_qn nd in
  let et =
    let n = N.Scope.get_name scope in
    if N.Scope.is_enumclass scope then
      I.ElaboratedType.EnumClass n
    else
      I.ElaboratedType.Enum n
  in
  let ts = I.TypeSpec.Elaborated et in
  let ty = I.Type.make_simple_type (new I.decl_specs) [ts] (I.TypeSpec.encode [ts]) in
  [nd, qn, ty]

and qn_type_list_of_mem_decl (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | MemberDeclarationDecl -> begin
      let sty = simple_type_of_decl_spec_seq (nd#nth_children 1) in
      [%debug_log "sty=%s" (Type.to_string sty)];
      match nd#nth_children 2 with
      | [] -> begin
          match Type.idents_of_simple_type sty with
          | [i] -> [nd, i, sty]
          | _ -> []
      end
      | l -> begin
          List.map
            (fun x ->
              let i, w = qn_wrap_of_mem_declarator x in
              x, i, w sty
            ) l
      end
  end
  | _ -> invalid_arg "Cpp.Ast.qn_type_list_of_mem_decl"

and qn_type_of_func_def (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | FunctionDefinition _ | FunctionHead _ -> begin
      let sty = simple_type_of_decl_spec_seq (nd#nth_children 1) in
      [%debug_log "sty=%s" (Type.to_string sty)];
      match nd#nth_children 2 with
      | [d] -> begin
          let i, w = qn_wrap_of_declarator d in
          let fty = w sty in
          [%debug_log "fty=%s" (Type.to_string fty)];
          let rec proc_ty = function
            | Type.FunctionTy x -> begin
                let v = x.Type.ft_virt_specs in
                try
                  List.iter
                    (fun (nd : node) ->
                      match nd#label with
                      | VirtSpecifierFinal -> v#set_final()
                      | VirtSpecifierOverride -> v#set_override()
                      | _ -> ()
                    ) (nd#nth_children 3)
                with _ -> ()
            end
            | Type.PointerTy x -> proc_ty x.Type.pt_type
            | Type.AltTy _ -> ()
            | _ -> ()
          in
          proc_ty fty;
          i, fty
      end
      | _ -> assert false
  end
  | _ -> invalid_arg "Cpp.Ast.qn_type_of_func_def"

and qn_wrap_of_init_declarator (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | InitDeclarator _ -> begin
      match nd#nth_children 1 with
      | [d] -> qn_wrap_of_declarator d
      | _ -> assert false
  end
  | PpIfSection _ -> begin
      let ns =
        ((nd#nth_child 0)#nth_child 1)::
        (List.map (fun x -> x#nth_child 1) (nd#nth_children 1)) @
        (List.map (fun x -> x#nth_child 1) (nd#nth_children 2))
      in
      let il, wl =
        List.split
          (List.filter_map
             (fun x ->
               match x#label with
               | L.InitDeclarator _ | PpIfSection _ -> Some (qn_wrap_of_init_declarator x)
               | _ -> None
             ) ns
          )
      in
      let i = String.concat "|" il in
      let w x = Type.make_alt_type (List.map (fun w -> w x) wl) in
      i, w
  end
  | _ -> invalid_arg "Cpp.Ast.qn_wrap_of_init_declarator"

and qn_wrap_of_mem_declarator (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | MemberDeclaratorDecl -> qn_wrap_of_declarator (nd#nth_child 0)
  | MemberDeclaratorBitField i -> i, fun x -> x
  | PpDefine _ -> "", fun x -> x
  | _ -> invalid_arg "Cpp.Ast.qn_wrap_of_mem_declarator"

and qn_wrap_of_declarator ?(ty_opt=None) (nd : node) =
  begin %debug_block
    [%debug_log "%s" (L.to_string nd#label)];
    match ty_opt with
    | Some ty -> [%debug_log "%s" (I.Type.to_string ty)];
    | None -> ()
  end;
  match nd#label with
  | DummyDtor -> "", fun x -> x
  | DtorMacro i -> mk_macro_id i, fun x -> x
  | PpIfSection _ -> begin
      let ns =
        ((nd#nth_child 0)#nth_child 1)::
        (List.map (fun x -> x#nth_child 1) (nd#nth_children 1)) @
        (List.map (fun x -> x#nth_child 1) (nd#nth_children 2))
      in
      let il, wl = List.split (List.map qn_wrap_of_declarator ns) in
      let i = String.concat "|" il in
      let w x = Type.make_alt_type (List.map (fun w -> w x) wl) in
      i, w
  end
  | DeclaratorFunc -> begin
      let w1 = wrap_of_params_and_quals (nd#nth_child 1) in
      let i, w0 = qn_wrap_of_declarator (nd#nth_child 0) in
      let t = type_of_trailing_ret_type (nd#nth_child 2) in
      i, fun _ -> w0 (w1 t)
  end
  | PtrDeclaratorPtr -> begin
      let qualifiers = qualifiers_of_node_list (nd#nth_children 0) in
      match nd#nth_children 3 with
      | [n2] -> begin
          match nd#nth_children 1 with
          | [] -> begin
              qn_wrap_of_declarator n2
          end
          | [n1] -> begin
              let op = pointer_op_of_node n1 in
              let i, w = qn_wrap_of_declarator n2 in
              i, fun x -> w (Type.make_pointer_type ~qualifiers op x)
          end
          | _ -> assert false
      end
      | _ -> assert false
  end
  | NoptrDeclarator -> begin
      let _, w1 =
        try
          qn_wrap_of_declarator (nd#nth_child 1)
        with
          _ -> "", fun x -> x
      in
      let n0 = nd#nth_child 0 in
      let i, w0 = qn_wrap_of_declarator n0 in
      let w =
        match n0#label with
        | NoptrDeclaratorParen | NoptrAbstractDeclaratorParen -> fun x -> w0 (w1 x)
        | _ -> fun x -> w1 (w0 x)
      in
      i, w
  end
  | NoptrDeclaratorId -> (qn_of_declarator_id (nd#nth_child 0)), fun x -> x
  | NoptrDeclaratorFunc -> begin
      let w1 =
        try
          wrap_of_params_and_quals (nd#nth_child 1)
        with
          _ -> fun x -> x
      in
      let n0 = nd#nth_child 0 in
      let i, w0 = qn_wrap_of_declarator n0 in
      let w =
        match n0#label with
        | NoptrDeclaratorParen | NoptrAbstractDeclaratorParen -> fun x -> w0 (w1 x)
        | _ -> fun x -> w1 (w0 x)
      in
      i, w
  end
  | PpIfSectionBrokenDtorFunc -> begin
      let w1 =
        match nd#nth_children 4 with
        | [pdc] -> begin
            let ptys, is_vararg =
              param_tys_and_is_vararg_of_param_decl_clause pdc
            in
            fun rty -> Type.make_function_type ~is_vararg ptys rty
        end
        | _ -> assert false
      in
      let i_w_list =
        List.map
          (fun g ->
            [%debug_log "%s" (L.to_string g#label)];
            let n0 =
              match g#nth_children 2 with
              | [x] -> x
              | _ -> assert false
            in
            let i, w0 = qn_wrap_of_declarator n0 in
            let w =
              match n0#label with
              | NoptrDeclaratorParen | NoptrAbstractDeclaratorParen -> fun x -> w0 (w1 x)
              | _ -> fun x -> w1 (w0 x)
            in
            i, w
          ) ((nd#nth_child 0) :: (nd#nth_children 1) @ (nd#nth_children 2))
      in
      let il, wl = List.split i_w_list in
      let i = String.concat "|" il in
      let w x = Type.make_alt_type (List.map (fun w -> w x) wl) in
      i, w
  end
  | NoptrDeclaratorOldFunc -> begin
      let ids =
        List.map
          (fun x ->
            match x#label with
            | L.Identifier s -> s
            | L.ParamDeclMacro i -> mk_macro_id i
            | L.PpIfSection _ -> begin
               match ((x#nth_child 0)#nth_child 1)#label with
               | L.Identifier s -> s
               | _ -> assert false
            end
            | _ -> assert false
          ) (nd#nth_children 1)
      in
      let find =
        let tbl = Hashtbl.create 0 in
        List.iter
          (fun x ->
            List.iter
              (fun (_, i, ty) ->
                Hashtbl.add tbl i ty
              ) (qn_type_list_of_simple_decl x)
          ) (nd#nth_children 2);
        Hashtbl.find tbl
      in
      let ptys =
        List.map (fun i -> try find i with Not_found -> Type.int_t) ids
      in
      let w1 = fun rty -> Type.make_function_type ptys rty in
      let n0 = nd#nth_child 0 in
      let i, w0 = qn_wrap_of_declarator n0 in
      let w =
        match n0#label with
        | NoptrDeclaratorParen | NoptrAbstractDeclaratorParen -> fun x -> w0 (w1 x)
        | _ -> fun x -> w1 (w0 x)
      in
      i, w
  end
  | NoptrDeclaratorArray -> begin
      let i, w = qn_wrap_of_declarator (nd#nth_child 0) in
      i, fun ty -> Type.make_array_type (w ty) 1
  end
  | NoptrDeclaratorParen -> qn_wrap_of_declarator (nd#nth_child 0)
  | AbstractDeclaratorFunc -> begin
      let i, w0 =
        match nd#nth_children 0 with
        | [] -> "", fun x -> x
        | [n0] -> qn_wrap_of_declarator n0
        | _ -> assert false
      in
      let w1 =
        match nd#nth_children 1 with
        | [n1] -> wrap_of_params_and_quals n1
        | _ -> assert false
      in
      let t =
        match nd#nth_children 2 with
        | [n2] -> type_of_trailing_ret_type n2
        | _ -> assert false
      in
      i, fun _ -> w0 (w1 t)
  end
  | PtrAbstractDeclaratorPtr -> begin
      let op =
        match nd#nth_children 1 with
        | [x] -> pointer_op_of_node x
        | _ -> assert false
      in
      match ty_opt with
      | Some ty -> begin
          match nd#nth_children 2 with
          | [] -> "", let x = Type.make_pointer_type op ty in fun _ -> x
          | [n] -> begin
              let i, w = qn_wrap_of_declarator ~ty_opt n in
              i, let x = Type.make_pointer_type op (w ty) in fun _ -> w x
          end
          | _ -> assert false
      end
      | None -> begin
          match nd#nth_children 2 with
          | [] -> "", Type.make_pointer_type op
          | [n] -> begin
              let i, w = qn_wrap_of_declarator n in
              i, fun x -> w (Type.make_pointer_type op (w x))
          end
          | _ -> assert false
      end
  end
  | NewDeclaratorPtr | ConversionDeclarator | AbstractPackDeclarator -> begin
      let op = pointer_op_of_node (nd#nth_child 0) in
      match nd#nth_children 1 with
      | [] -> "", Type.make_pointer_type op
      | [n] -> begin
          let i, w = qn_wrap_of_declarator n in
          i, fun x -> w (Type.make_pointer_type op (w x))
      end
      | _ -> assert false
  end
  | NoptrAbstractDeclaratorFunc -> begin
      let w1 =
        match nd#nth_children 1 with
        | [n1] -> wrap_of_params_and_quals n1
        | _ -> assert false
      in
      match nd#nth_children 0 with
      | [] -> "", w1
      | [n0] -> begin
          let i, w0 = qn_wrap_of_declarator n0 in
          let w =
            match n0#label with
            | NoptrDeclaratorParen | NoptrAbstractDeclaratorParen -> fun x -> w0 (w1 x)
            | _ -> fun x -> w1 (w0 x)
          in
          i, w
      end
      | _ -> assert false
  end
  | NoptrAbstractDeclaratorArray -> begin
      let i, w =
        match nd#nth_children 0 with
        | [] -> "", fun x -> x
        | [n] -> qn_wrap_of_declarator n
        | _ -> assert false
      in
      i, fun x -> Type.make_array_type (w x) 1
  end
  | NoptrAbstractDeclaratorParen -> qn_wrap_of_declarator (nd#nth_child 0)
  | NoptrNewDeclarator -> begin
      let i, w =
        match nd#nth_children 0 with
        | [] -> "", fun x -> x
        | [n] -> qn_wrap_of_declarator n
        | _ -> assert false
      in
      i, fun x -> Type.make_array_type (w x) 1
  end
  | NoptrAbstractPackDeclaratorFunc -> begin
      let w1 = wrap_of_params_and_quals (nd#nth_child 1) in
      let _, w0 = qn_wrap_of_declarator (nd#nth_child 0) in
      "", fun x -> w1 (w0 x)
  end
  | NoptrAbstractPackDeclaratorArray -> begin
      let _, w = qn_wrap_of_declarator (nd#nth_child 0) in
      "", fun x -> Type.make_array_type (w x) 1
  end
  | AbstractPack -> "", fun x -> x

  | InitDeclarator _ -> qn_wrap_of_declarator (nd#nth_child 0)

  | _ -> invalid_arg "Cpp.Ast.qn_wrap_of_declarator"

and type_of_trailing_ret_type (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | TrailingReturnType -> type_of_type_id (nd#nth_child 0)
  | _ -> invalid_arg "Cpp.Ast.type_of_trailing_return_type"

and type_of_type_id (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | TypeId | NewTypeId | ConversionTypeId -> begin
      let sty = simple_type_of_decl_spec_seq (nd#nth_children 0) in
      match nd#nth_children 1 with
      | [] -> sty
      | [n] -> begin
          let _, w = qn_wrap_of_declarator n in
          w sty
      end
      | _ -> assert false
  end
  | _ -> invalid_arg "Cpp.Ast.type_of_type_id"

and wrap_of_params_and_quals (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | ParametersAndQualifiers -> begin
      let ptys, is_vararg =
        param_tys_and_is_vararg_of_param_decl_clause (nd#nth_child 0)
      in
      let qs = (nd#nth_children 1) @ (nd#nth_children 2) @ (nd#nth_children 3) in
      let qualifiers = qualifiers_of_node_list qs in
      fun rty -> Type.make_function_type ~qualifiers ~is_vararg ptys rty
  end
  | ParametersMacro p -> fun rty -> Type.make_function_type ~params_macro:p [] rty
  | ParametersMacroInvocation p -> begin
      match nd#children with
      | [n0] -> begin
          match n0#label with
          | MacroArgument -> begin
              match n0#children with
              | [n00] -> begin
                  match n00#label with
                  | ParametersAndQualifiers -> wrap_of_params_and_quals n00
                  | _ -> fun rty -> Type.make_function_type ~params_macro:p [] rty
              end
              | _ -> fun rty -> Type.make_function_type ~params_macro:p [] rty
          end
          | _ -> assert false
      end
      | _ -> fun rty -> Type.make_function_type ~params_macro:p [] rty
  end
  | _ -> invalid_arg "Cpp.Ast.wrap_of_params_and_quals"

and param_tys_and_is_vararg_of_param_decl_clause (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | ParameterDeclarationClause b -> begin
      match nd#children with
      | [] -> [], b
      | [n] -> begin
          match n#label with
          | ParameterDeclaration _ -> begin
              try
                let ty = type_of_param_decl n in
                [ty], b
              with
                _ -> [], b
          end
          | _ -> assert false
      end
      | l ->
          (Xlist.filter_map (fun x -> try Some (type_of_param_decl x) with _ -> None) l), b
  end
  | _ -> invalid_arg "Cpp.Ast.param_tys_of_param_decl_clause"

and type_of_param_decl (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  let _, _, ty = qn_type_of_param_decl nd in
  ty

and qn_type_of_param_decl (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  let il, tl =
    List.fold_left
      (fun (il, tl) (_, i, t) ->
        i::il, t::tl
      ) ([], []) (qn_type_list_of_param_decl nd)
  in
  let i = String.concat "|" il in
  let t =
    match tl with
    | [] -> raise Not_found
    | [t] -> t
    | _ -> Type.make_alt_type tl
  in
  nd, i, t

and qn_type_list_of_param_decl (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | ParameterDeclaration _ -> begin
      let sty = simple_type_of_decl_spec_seq (nd#nth_children 1) in
      let qn, wrap =
        match nd#nth_children 2 with
        | [n] -> qn_wrap_of_declarator ~ty_opt:(Some sty) n
        | _ -> "", fun x -> x
      in
      [nd, qn, wrap sty]
  end
  | PpIfSection _ -> begin
      let if_itl = try [qn_type_of_param_decl ((nd#nth_child 0)#nth_child 1)] with _ -> [] in
      let elif_itl =
        Xlist.filter_map
          (fun x -> try Some (qn_type_of_param_decl (x#nth_child 1)) with _ -> None)
          (nd#nth_children 1)
      in
      let else_itl =
        Xlist.filter_map
          (fun x -> try Some (qn_type_of_param_decl (x#nth_child 1)) with _ -> None)
          (nd#nth_children 2)
      in
      if_itl @ elif_itl @ else_itl
  end
  | ParamDeclMacro _ | ParamDeclMacroInvocation _ -> []
  | _ -> []
  (*| _ -> invalid_arg "Cpp.Ast.qn_type_list_of_param_decl"*)

and qn_type_of_exc_decl (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | ExceptionDeclaration -> begin
      let sty = simple_type_of_decl_spec_seq (nd#nth_children 1) in
      let qn, wrap =
        match nd#nth_children 2 with
        | [n] -> qn_wrap_of_declarator n
        | _ -> "", fun x -> x
      in
      nd, qn, wrap sty
  end
  | Ellipsis -> raise Type_not_found
  | _ -> invalid_arg "Cpp.Ast.qn_type_of_exc_decl"

and enum_base_of_node (*ns*)_ (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | EnumBase -> new N.Spec.enum_base (type_spec_list_of_node_list nd#children)
  | BaseMacro i -> new N.Spec.enum_base ~macro_name:i []
  | _ -> invalid_arg "Cpp.Ast.enum_base_of_node"

and type_spec_of_node ?(ns="") (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  match nd#label with
  | SimpleTypeSpecifier uqn -> begin
      let prefix =
        match nd#nth_children 0 with
        | [] -> ns
        | [n0] -> ns^(encode_nested_name_spec n0)
        | _ -> assert false
      in
      let fqn = prefix^uqn in
      [%debug_log "fqn=%s" fqn];
      I.TypeSpec.Simple fqn
  end
  | DecltypeSpecifier                -> I.TypeSpec.Decltype (encode_decltype nd)
  | PlaceholderTypeSpecifierAuto     -> I.TypeSpec.Placeholder I.PlaceholderType.Auto
  | PlaceholderTypeSpecifierDecltype -> I.TypeSpec.Placeholder I.PlaceholderType.Decltype
  | Char     -> I.TypeSpec.Char
  | Char8_t  -> I.TypeSpec.Char8_t
  | Char16_t -> I.TypeSpec.Char16_t
  | Char32_t -> I.TypeSpec.Char32_t
  | Wchar_t  -> I.TypeSpec.Wchar_t
  | Bool     -> I.TypeSpec.Bool
  | Short    -> I.TypeSpec.Short
  | Int      -> I.TypeSpec.Int
  | Long     -> I.TypeSpec.Long
  | Signed   -> I.TypeSpec.Signed
  | Unsigned -> I.TypeSpec.Unsigned
  | Float    -> I.TypeSpec.Float
  | Double   -> I.TypeSpec.Double
  | Void     -> I.TypeSpec.Void
  | UnsignedInt  -> I.TypeSpec.UnsignedInt
  | UnsignedLong -> I.TypeSpec.UnsignedLong
  | ElaboratedTypeSpecifierClass u  -> I.TypeSpec.Elaborated (I.ElaboratedType.Class (ns^u))
  | ElaboratedTypeSpecifierStruct u -> I.TypeSpec.Elaborated (I.ElaboratedType.Struct (ns^u))
  | ElaboratedTypeSpecifierUnion u  -> I.TypeSpec.Elaborated (I.ElaboratedType.Union (ns^u))
  | ElaboratedTypeSpecifierEnum u   -> I.TypeSpec.Elaborated (I.ElaboratedType.Enum (ns^u))
  | TypenameSpecifier uqn -> I.TypeSpec.Typename (ns^uqn)
  | Const    -> I.TypeSpec.CvQualifier I.CvQualifier.Const
  | Volatile -> I.TypeSpec.CvQualifier I.CvQualifier.Volatile
  | Restrict _  -> I.TypeSpec.CvQualifier I.CvQualifier.Restrict
  | MsCdecl _   -> I.TypeSpec.CvQualifier I.CvQualifier.Cdecl
  | MsStdcall _ -> I.TypeSpec.CvQualifier I.CvQualifier.Stdcall
  | _ -> invalid_arg "Cpp.Ast.type_spec_of_node"

and simple_type_of_class_head (nd : node) =
  [%debug_log "%s" (L.to_string nd#label)];
  try
    let is_macro = ref false in
    let k =
      match nd#label with
      | ClassHeadClass  -> fun x -> I.ElaboratedType.Class x
      | ClassHeadStruct -> fun x -> I.ElaboratedType.Struct x
      | ClassHeadUnion  -> fun x -> I.ElaboratedType.Union x
      | ClassHeadMacro i           -> is_macro := true; fun _ -> I.ElaboratedType.Macro (mk_macro_id i)
      | ClassHeadMacroInvocation i -> is_macro := true; fun _ -> I.ElaboratedType.Macro (mk_macro_call_id i)
      | PpIfSection _   -> raise Exit
      (*| _ -> raise Not_found*)
      | _ -> assert false
    in
    let n =
      match nd#nth_children 1 with
      | _ when !is_macro -> ""
      | [] -> ""
      | [x] -> begin
          match x#label with
          | ClassName uqn -> uqn
          | ClassHeadName qn -> (encode_nested_name_spec (x#nth_child 0))^qn
          | IdentifierMacroInvocation i ->
              let args = args_to_simple_string x#children in
              mk_macro_call_id ~args i
          | _ -> assert false
      end
      | _ -> assert false
    in
    [I.TypeSpec.Elaborated (k n)]
  with
  (*| Not_found -> []*)
  | Exit ->
      let g x = x#nth_child 1 in
      let chs =
        (g (nd#nth_child 0))::
        (List.map g (nd#nth_children 1)) @ (List.map g (nd#nth_children 2))
      in
      List.concat_map simple_type_of_class_head chs

and simple_type_of_decl_spec_seq (nds : node list) =
  [%debug_log "nds=[%s]" (String.concat "; " (List.map (fun n -> L.to_string n#label) nds))];
  match nds with
  | [n] when begin
      match n#label with
      | DeclSpecifierSeq -> true
      | _ -> false
  end -> simple_type_of_decl_spec_seq (n#nth_children 0)
  | _ ->
  let ds = new I.decl_specs in
  let ts =
    List.fold_left
      (fun ts (x : node) ->
        [%debug_log "%s" (L.to_string x#label)];
        match x#label with
        | StorageClassSpecifierStatic -> ds#set_storage_class_static(); ts
        | StorageClassSpecifierThread_local -> ds#set_storage_class_thread_local(); ts
        | StorageClassSpecifierExtern -> ds#set_storage_class_extern(); ts
        | StorageClassSpecifierMutable -> ds#set_storage_class_mutable(); ts
        | FunctionSpecifierVirtual -> ds#set_function_spec_virtual(); ts
        | ExplicitSpecifier -> ds#set_function_spec_explicit(); ts
        | DeclSpecifierFriend -> ds#set_friend(); ts
        | DeclSpecifierTypedef -> ds#set_typedef(); ts
        | DeclSpecifierConstexpr -> ds#set_constexpr(); ts
        | DeclSpecifierConsteval -> ds#set_consteval(); ts
        | DeclSpecifierInline -> ds#set_inline(); ts

        | SimpleTypeSpecifier _
        | DecltypeSpecifier
        | PlaceholderTypeSpecifierAuto | PlaceholderTypeSpecifierDecltype
        | Char | Char8_t | Char16_t | Char32_t | Wchar_t | Bool | Short | Int | Long
        | Signed | Unsigned | Float | Double | Void
        | Const | Volatile -> (type_spec_of_node x)::ts

        | ElaboratedTypeSpecifierClass _ | ElaboratedTypeSpecifierStruct _
        | ElaboratedTypeSpecifierUnion _ | ElaboratedTypeSpecifierEnum _ ->
            let ns =
              try
                encode_nested_name_spec (List.hd (x#nth_children 1))
              with _ -> ""
            in
            (type_spec_of_node ~ns x)::ts

        | TypenameSpecifier _ ->
            let ns =
              try
                encode_nested_name_spec (List.hd (x#nth_children 0))
              with _ -> ""
            in
            (type_spec_of_node ~ns x)::ts

        | ClassSpecifier -> begin
            match x#nth_children 1 with
            | [y] -> (simple_type_of_class_head y)@ts
            | _ -> assert false
        end
        | EnumSpecifier -> begin
            match x#nth_children 1 with
            | [y] -> begin
                let k =
                  match y#label with
                  | EnumHeadEnum
                  | EnumHeadEnumMacro _ -> fun x -> I.ElaboratedType.Enum x
                  | EnumHeadEnumClass
                  | EnumHeadEnumStruct -> fun x -> I.ElaboratedType.EnumClass x
                  | lab ->
                      let _ = lab in
                      [%debug_log "%s" (L.to_string lab)];
                      assert false
                in
                let n =
                  match y#nth_children 1 with
                  | [] -> ""
                  | [z] -> begin
                      match z#label with
                      | EnumHeadName qn when z#children = [] -> qn
                      | EnumHeadName qn -> (encode_nested_name_spec (List.hd z#children))^qn
                      | _ -> assert false
                  end
                  | _ -> [%debug_log "@"]; assert false
                in
                (I.TypeSpec.Elaborated (k n))::ts
            end
            | _ -> assert false
        end
        | _ -> ts
      ) [] nds
  in
  [%debug_log "ts=[%s]" (String.concat "; " (List.map I.TypeSpec.to_string ts))];
  let encoded = I.TypeSpec.encode ts in
  Type.make_simple_type ds ts encoded
]


class c (root : node) = object
  inherit Ast_base.c

  method root = root

end (* class Ast.c *)


let dummy_node = new node L.DUMMY
let empty_node = new node L.EMPTY

let subtree_to_string root =
  let buf = Buffer.create 0 in
  let rec doit ind nd =
    Buffer.add_string buf (sprintf "%s%s\n" ind nd#to_string);
    List.iter (doit (ind^"  ")) nd#children
  in
  doit "" root;
  Buffer.contents buf

let to_string ast =
  subtree_to_string ast#root

let dump ast =
  let rec doit ind nd =
    printf "%s%s\n" ind nd#to_string;
    List.iter (doit (ind^"  ")) nd#children
  in
  doit "" ast#root

let iter f (ast : c) =
  let rec doit nd =
    f nd;
    List.iter doit nd#children
  in
  doit ast#root
