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
(* parser_aux.ml *)

[%%prepare_logger]

module Xlist = Diffast_misc.Xlist
module Xset = Diffast_misc.Xset
module Env_base = Langs_common.Env_base
module Source_base = Langs_common.Source_base
module Astloc = Langs_common.Astloc

open Printf
open Common
open Ast

module P = Printer

exception Attrs_found of identifier_attribute list
exception Unknown of string
exception Type_found of string
exception Expr_found of expr_kind
exception Static_found of string

type sub_context =
  | SC_block
  | SC_new
  | SC_ivk
  | SC_for
  | SC_array
  | SC_lambda
  | SC_res

type meth_stat = {
    mutable m_block_level: int;
    mutable m_paren_level: int;
    mutable m_new_level: int;
    mutable m_ivk_level: int;
    mutable m_for_level: int;
    mutable m_array_level: int; (* array initializer *)
    mutable m_lambda_level: int;
    mutable m_tap_level: int;
    mutable m_res_level: int;
    m_stack: sub_context Stack.t
}

type class_stat = {
    mutable c_tap_level: int;
}

type top_stat = {
    mutable t_tap_level: int;
}

let create_class_stat () =
  { c_tap_level=0;
  }

let create_top_stat () =
  { t_tap_level=0;
  }

let create_meth_stat () =
  { m_block_level=0;
    m_paren_level=0;
    m_new_level=0;
    m_ivk_level=0;
    m_for_level=0;
    m_array_level=0;
    m_lambda_level=0;
    m_tap_level=0;
    m_res_level=0;
    m_stack=Stack.create();
  }

type context =
  | C_toplevel of top_stat
  | C_class of class_stat
  | C_method of meth_stat
  | C_module

let stack_to_list stack = List.rev (Stack.fold (fun l x -> x::l) [] stack)

let sub_context_to_string = function
  | SC_block  -> "B"
  | SC_new    -> "N"
  | SC_ivk    -> "I"
  | SC_for    -> "F"
  | SC_array  -> "A"
  | SC_lambda -> "L"
  | SC_res    -> "R"

let meth_stat_to_string { m_block_level=blv;
                          m_paren_level=plv;
                          m_new_level=nlv;
                          m_ivk_level=ilv;
                          m_for_level=flv;
                          m_array_level=alv;
                          m_lambda_level=llv;
                          m_tap_level=tlv;
                          m_res_level=rlv;
                          m_stack=stack;
                        } =
  let s = String.concat "" (List.map sub_context_to_string (stack_to_list stack)) in
  Printf.sprintf "{B:%d,P:%d,N:%d,I:%d,F:%d,A:%d,L:%d,T:%d,R:%d,%s}" blv plv nlv ilv flv alv llv tlv rlv s

let class_stat_to_string { c_tap_level=tlv;
                         } =
  Printf.sprintf "{T:%d}" tlv

let top_stat_to_string { t_tap_level=tlv;
                       } =
  Printf.sprintf "{T:%d}" tlv

let context_to_string = function
  | C_toplevel tstat -> Printf.sprintf "T:%s" (top_stat_to_string tstat)
  | C_class cstat -> Printf.sprintf "C:%s" (class_stat_to_string cstat)
  | C_method mstat -> Printf.sprintf "M:%s" (meth_stat_to_string mstat)
  | C_module -> Printf.sprintf "MOD"

let stack_memq stack x =
  try
    Stack.iter (fun y -> if y == x then raise Exit) stack;
    false
  with
    Exit -> true

exception Frame_found of frame


[%%capture_path
class env = object (self)
  inherit [Source_base.c] Env_base.c as super

  val mutable java_lang_spec = default_java_lang_spec
  val mutable actual_java_lang_spec = JLSnone

  val mutable current_package_name = ""

  val classtbl = new Classinfo.classtbl_c

  val stack = Stack.create()

  val mutable last_rawtoken = Obj.repr ()

  val mutable last_td_end_opt = (None : (Lexing.position * string) option)

  val mutable global_frame = new frame FKother

  val mutable rely_on_naming_convention_flag = false
  val mutable partial_name_resolution_flag = false
  val mutable partial_typename_resolution_flag = false
  val mutable no_implicit_name_resolution_flag = false

  val mutable lex_brace_level = 0
  val mutable class_flag = false
  val mutable shift_flag = false
  val mutable stmt_head_flag = false

  val mutable in_aspect_flag = false
  val mutable in_declare_flag = false
  val mutable in_pointcut_flag = false

  val mutable case_flag = false

  val mutable g_brace_level = 0

  val context_stack = Stack.create ()

  val mutable nintegers = -1
  val mutable nfloats   = -1
  val mutable nstrings  = -1

  method incr_nintegers() =
    if nintegers < 0 then
      nintegers <- 1
    else
      nintegers <- nintegers + 1
  method incr_nfloats() =
    if nfloats < 0 then
      nfloats <- 1
    else
      nfloats <- nfloats + 1
  method incr_nstrings() =
    if nstrings < 0 then
      nstrings <- 1
    else
      nstrings <- nstrings + 1

  method nintegers = nintegers
  method nfloats = nfloats
  method nstrings = nstrings

  method in_declare_flag = in_declare_flag

  method set_in_declare_flag =
    [%debug_log "set"];
    in_declare_flag <- true

  method clear_in_declare_flag =
    [%debug_log "clear"];
    in_declare_flag <- false

  method in_pointcut_flag = in_pointcut_flag

  method set_in_pointcut_flag =
    [%debug_log "set"];
    in_pointcut_flag <- true

  method clear_in_pointcut_flag =
    [%debug_log "clear"];
    in_pointcut_flag <- false

  method case_flag = case_flag

  method set_case_flag =
    [%debug_log "set"];
    case_flag <- true

  method clear_case_flag =
    [%debug_log "clear"];
    case_flag <- false

  method shift_flag = shift_flag

  method set_shift_flag =
    [%debug_log "set"];
    shift_flag <- true

  method clear_shift_flag =
    [%debug_log "clear"];
    shift_flag <- false

  method stmt_head_flag = stmt_head_flag

  method set_stmt_head_flag =
    [%debug_log "set"];
    stmt_head_flag <- true

  method clear_stmt_head_flag =
    [%debug_log "clear"];
    stmt_head_flag <- false

  method class_flag = class_flag

  method set_class_flag =
    [%debug_log "set"];
    class_flag <- true

  method clear_class_flag =
    [%debug_log "clear"];
    class_flag <- false

  method in_aspect_flag = in_aspect_flag

  method set_in_aspect_flag =
    [%debug_log "set"];
    in_aspect_flag <- true

  method clear_in_aspect_flag =
    [%debug_log "clear"];
    in_aspect_flag <- false

  method context_stack_rep =
    let buf = Buffer.create 0 in
    Stack.iter
      (fun c ->
        Buffer.add_string buf (context_to_string c)
      ) context_stack;
    Buffer.contents buf

  method context_stack_as_list =
    stack_to_list context_stack

  method enter_class =
    [%debug_log "enter"];
    Stack.push (C_class (create_class_stat())) context_stack;
    [%debug_log "context_stack: %s" self#context_stack_rep]

  method enter_module =
    [%debug_log "enter"];
    Stack.push C_module context_stack;
    [%debug_log "context_stack: %s" self#context_stack_rep]

  method enter_method =
    [%debug_log "enter"];
    Stack.push (C_method (create_meth_stat())) context_stack;
    [%debug_log "context_stack: %s" self#context_stack_rep]

  method exit_context =
    [%debug_log "exit"];
    ignore (Stack.pop context_stack);
    [%debug_log "context_stack: %s" self#context_stack_rep]

  method current_context =
    Stack.top context_stack

  method in_method =
    [%debug_log "context_stack: %s" self#context_stack_rep];
    match Stack.top context_stack with
    | C_method _ -> true
    | _ -> false

  method in_class =
    [%debug_log "context_stack: %s" self#context_stack_rep];
    match Stack.top context_stack with
    | C_class _ -> true
    | _ -> false

  method in_module =
    [%debug_log "context_stack: %s" self#context_stack_rep];
    match Stack.top context_stack with
    | C_module -> true
    | _ -> false

  method rely_on_naming_convention_flag = rely_on_naming_convention_flag
  method _set_rely_on_naming_convention_flag b = rely_on_naming_convention_flag <- b

  method partial_name_resolution_flag = partial_name_resolution_flag
  method _set_partial_name_resolution_flag b = partial_name_resolution_flag <- b

  method partial_typename_resolution_flag = partial_typename_resolution_flag
  method _set_partial_typename_resolution_flag b = partial_typename_resolution_flag <- b

  method no_implicit_name_resolution_flag = no_implicit_name_resolution_flag
  method _set_no_implicit_name_resolution_flag b = no_implicit_name_resolution_flag <- b

  method at_res =
    begin
      match self#current_context with
      | C_method mstat -> stack_memq mstat.m_stack SC_res
      | _ -> false
    end

  method at_lambda =
    begin
      match self#current_context with
      | C_method mstat -> stack_memq mstat.m_stack SC_lambda
      | _ -> false
    end

  method at_array =
    begin
      match self#current_context with
      | C_method mstat -> stack_memq mstat.m_stack SC_array
      | _ -> false
    end

  method at_new =
    begin
      match self#current_context with
      | C_method mstat -> Stack.top mstat.m_stack = SC_new
      | _ -> false
    end

  method at_for =
    begin
      match self#current_context with
      | C_method mstat -> stack_memq mstat.m_stack SC_for
      | _ -> false
    end

  method at_block =
    begin
      match self#current_context with
      | C_method mstat -> Stack.top mstat.m_stack = SC_block
      | _ -> false
    end

  method g_brace_level = g_brace_level

  method g_open_brace =
    g_brace_level <- g_brace_level + 1

  method g_close_brace =
    g_brace_level <- g_brace_level - 1

  method res_level =
    [%debug_log "context_stack: %s" (self#context_stack_rep)];
    match self#current_context with
    | C_method mstat -> mstat.m_res_level
    | _ -> 0

  method in_res = self#res_level > 0

  method open_res =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_res_level <- mstat.m_res_level + 1;
          Stack.push SC_res mstat.m_stack
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method close_res =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_res_level <- mstat.m_res_level - 1;
          ignore (Stack.pop mstat.m_stack)
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method tap_level =
    [%debug_log "context_stack: %s" (self#context_stack_rep)];
    match self#current_context with
    | C_method mstat -> mstat.m_tap_level
    | C_class cstat -> cstat.c_tap_level
    | C_toplevel tstat -> tstat.t_tap_level
    | C_module -> 0

  method in_tap = self#tap_level > 0

  method open_tap =
    begin
      match self#current_context with
      | C_method mstat -> mstat.m_tap_level <- mstat.m_tap_level + 1
      | C_class cstat -> cstat.c_tap_level <- cstat.c_tap_level + 1
      | C_toplevel tstat -> tstat.t_tap_level <- tstat.t_tap_level + 1
      | C_module -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method close_tap =
    begin
      match self#current_context with
      | C_method mstat -> mstat.m_tap_level <- mstat.m_tap_level - 1
      | C_class cstat -> cstat.c_tap_level <- cstat.c_tap_level - 1
      | C_toplevel tstat -> tstat.t_tap_level <- tstat.t_tap_level - 1
      | C_module -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method lambda_level =
    [%debug_log "context_stack: %s" (self#context_stack_rep)];
    match self#current_context with
    | C_method mstat -> mstat.m_lambda_level
    | _ -> 0

  method in_lambda = self#lambda_level > 0

  method enter_lambda =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_lambda_level <- mstat.m_lambda_level + 1;
          Stack.push SC_lambda mstat.m_stack
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method exit_lambda =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_lambda_level <- mstat.m_lambda_level - 1;
          ignore (Stack.pop mstat.m_stack)
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method array_level =
    [%debug_log "context_stack: %s" (self#context_stack_rep)];
    match self#current_context with
    | C_method mstat -> mstat.m_array_level
    | _ -> 0

  method in_array = self#array_level > 0

  method enter_array =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_array_level <- mstat.m_array_level + 1;
          Stack.push SC_array mstat.m_stack
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method exit_array =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_array_level <- mstat.m_array_level - 1;
          ignore (Stack.pop mstat.m_stack)
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method new_level =
    [%debug_log "context_stack: %s" (self#context_stack_rep)];
    match self#current_context with
    | C_method mstat -> mstat.m_new_level
    | _ -> 0

  method in_new = self#new_level > 0

  method enter_new =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_new_level <- mstat.m_new_level + 1;
          Stack.push SC_new mstat.m_stack
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method exit_new =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_new_level <- mstat.m_new_level - 1;
          ignore (Stack.pop mstat.m_stack)
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method ivk_level =
    [%debug_log "context_stack: %s" (self#context_stack_rep)];
    match self#current_context with
    | C_method mstat -> mstat.m_ivk_level
    | _ -> 0

  method in_ivk = self#ivk_level > 0

  method enter_ivk =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_ivk_level <- mstat.m_ivk_level + 1;
          Stack.push SC_ivk mstat.m_stack
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method exit_ivk =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_ivk_level <- mstat.m_ivk_level - 1;
          ignore (Stack.pop mstat.m_stack)
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method in_for = self#for_level > 0

  method for_level =
    [%debug_log "context_stack: %s" (self#context_stack_rep)];
    match self#current_context with
    | C_method mstat -> mstat.m_for_level
    | _ -> 0

  method enter_for =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_for_level <- mstat.m_for_level + 1;
          Stack.push SC_for mstat.m_stack
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method exit_for =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_for_level <- mstat.m_for_level - 1;
          ignore (Stack.pop mstat.m_stack)
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method block_level =
    [%debug_log "context_stack: %s" (self#context_stack_rep)];
    match self#current_context with
    | C_method mstat -> mstat.m_block_level
    | _ -> 0

  method open_block =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_block_level <- mstat.m_block_level + 1;
          Stack.push SC_block mstat.m_stack
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method close_block =
    begin
      match self#current_context with
      | C_method mstat ->
          mstat.m_block_level <- mstat.m_block_level - 1;
          ignore (Stack.pop mstat.m_stack)
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method paren_level =
    match self#current_context with
    | C_method mstat -> mstat.m_paren_level
    | _ -> 0

  method open_paren =
    begin
      match self#current_context with
      | C_method mstat -> mstat.m_paren_level <- mstat.m_paren_level + 1
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method close_paren =
    begin
      match self#current_context with
      | C_method mstat -> mstat.m_paren_level <- mstat.m_paren_level - 1
      | _ -> ()
    end;
    [%debug_log "context_stack: %s" (self#context_stack_rep)]

  method lex_brace_level = lex_brace_level
  method reset_lex_brace_level = lex_brace_level <- 0
  method open_lex_brace = lex_brace_level <- lex_brace_level + 1
  method close_lex_brace = lex_brace_level <- lex_brace_level - 1

  method get_global_frame = global_frame

  method last_rawtoken = last_rawtoken
  method set_last_rawtoken o = last_rawtoken <- o

  method last_td_end_opt = last_td_end_opt
  method set_last_td_end p s = last_td_end_opt <- Some (p, s)
  method clear_last_td_end = last_td_end_opt <- None

  method classtbl = classtbl

  method java_lang_spec = java_lang_spec
  method set_java_lang_spec lv = java_lang_spec <- JLS lv
  method reset_java_lang_spec = java_lang_spec <- default_java_lang_spec

  method actual_java_lang_spec = actual_java_lang_spec
  method set_actual_java_lang_spec lv =
    match actual_java_lang_spec with
    | JLSnone -> actual_java_lang_spec <- JLS lv
    | JLS x when lv > x -> actual_java_lang_spec <- JLS lv
    | _ -> ()
  method reset_actual_java_lang_spec = java_lang_spec <- JLSnone

  method set_current_package_name n =
    current_package_name <- n

  method current_package_name = current_package_name

  method begin_scope ?(kind=FKother) ?(frame_opt=None) () =
    [%debug_log "PUSH %s (%d)" (frame_kind_to_string kind) (Stack.length stack)];
    let frame =
      match frame_opt with
      | None -> new frame kind
      | Some f -> f
    in
    Stack.push frame stack

  method end_scope() =
    [%debug_log "POP (%d)" (Stack.length stack)];
    try
      let _(*frm*) = Stack.pop stack in
      (*if is_class_frame frm#kind && self#in_class then begin
      end*)()
    with
      Stack.Empty ->
        raise (Internal_error "Parser_aux.end_scope: stack empty")

  method current_frame =
    try
      Stack.top stack
    with
      Stack.Empty ->
        raise (Internal_error "Parser_aux.current_frame: stack empty")

  method set_has_super() =
    try
      match self#current_frame#kind with
      | FKclass(_, x) -> [%debug_log "@"]; x := true
      | _ -> ()
    with _ -> ()

  method set_is_static() =
    try
      match self#current_frame#kind with
      | FKmethod(_, x) -> x := true
      | _ -> ()
    with _ -> ()

  method has_super =
    try
      let frame = self#find_frame is_class_frame in
      match frame#kind with
      | FKclass(_, has_super) -> !has_super
      | _ -> false
    with _ -> false

  method in_static_method =
    try
      let frame = self#find_frame is_method_frame in
      match frame#kind with
      | FKmethod(_, is_static) -> !is_static
      | _ -> false
    with _ -> false

  method peek_frame skip =
    if skip < 0 then
      invalid_arg "Parser_aux.env#peek_frame"
    else if skip = 0 then
      self#current_frame
    else
      let count = ref 0 in
      try
        Stack.iter
          (fun f ->
            if !count >= skip then
              raise (Frame_found f)
            else
              incr count
          ) stack;
        assert false
      with
        Frame_found f -> f

  method copy_current_stack =
    Stack.copy stack

  method private get_frame ?(skip=0) attr =
    [%debug_log "skip=%d" skip];
    if attr <> IAtypeparameter && self#current_frame#is_typeparameter_frame then begin
      [%debug_log "@typeparameter_frame"];
      let count = ref 0 in
      try
        Stack.iter
          (fun f ->
            if !count >= skip then begin
              if not f#is_typeparameter_frame then
                raise (Frame_found f)
            end
            else
              incr count
          ) stack;
        assert false
      with
        Frame_found f -> f
    end
    else
      self#peek_frame skip

  method private find_frame ?(outer=0) filt =
    let count = ref 0 in
    let flag = ref false in
    try
      Stack.iter
        (fun f ->
          if !flag then incr count;
          if !flag && !count >= outer then raise (Frame_found f);
          if filt f#kind then begin
            flag := true;
            if outer = 0 then raise (Frame_found f)
          end
        ) stack;
      raise Not_found
    with
      Frame_found f -> f

  method register_identifier ?(qualify=false) ?(skip=0) ident attr =
    [%debug_log "REGISTER(%d): \"%s\" -> %s"
      ((Stack.length stack) - skip) ident (iattr_to_str attr)];

    let frame = self#get_frame ~skip attr in
    frame#add ident attr;

    if qualify then begin
      let class_names = self#surrounding_class_names in
      [%debug_log "class_names=[%s]" (String.concat "," class_names)];
      let rec iter = function
        | [] -> ()
        | (_ :: t) as l ->
            let n = (String.concat "." l)^"."^ident in
            let skip = skip + (List.length l) in
            [%debug_log "n=%s, skip=%d" n skip];
            let f = self#get_frame ~skip attr in
            [%debug_log "%s" f#to_string];
            f#qadd n attr;
            iter t
      in
      iter class_names
    end


  method lookup_identifier ?(afilt=(fun _ -> true)) ident =
    [%debug_log "LOOKUP(%d): \"%s\"" (Stack.length stack) ident];
    try
      Stack.iter
        (fun frame ->
          (*[%debug_log "%s" frame#to_string];*)
          try
            let attrs = frame#find_all ident in
            let filtered = List.filter afilt attrs in
            if filtered <> [] then
              raise (Attrs_found filtered)
          with
            Not_found -> ()
        ) stack;
      raise Not_found
    with
      Attrs_found attrs ->
        if attrs = [] then
          raise Not_found
        else begin
          [%debug_log "FOUND: %s -> [%s]" ident (Xlist.to_string iattr_to_str ";" attrs)];
          List.map
            (function
              | IAclass s | IAinterface s | IAtypename s as attr -> begin
                  try
                    let prefix = String.sub s 0 ((String.length s) - (String.length ident)) in
                    [%debug_log "prefix=\"%s\" ident=\"%s\"" prefix ident];
                    if String.ends_with ~suffix:"." prefix then begin
                      let sup = String.sub prefix 0 (String.length prefix - 1) in
                      let _, id = decompose_qname sup in
                      if id = ident then
                        attr
                      else begin
                        let afilt = function
                          | IAclass _ | IAinterface _ | IAtypename _ -> true
                          | _ -> false
                        in
                        try
                          let _ = self#lookup_identifier ~afilt id in
                          let x = sup ^ "$" ^ ident in
                          let attr' =
                            match attr with
                            | IAclass _ -> IAclass x
                            | IAinterface _ -> IAinterface x
                            | IAtypename _ -> IAtypename x
                            | _ -> assert false
                          in
                          [%debug_log "%s --> %s" (iattr_to_str attr) (iattr_to_str attr')];
                          attr'
                        with
                          Not_found -> attr
                      end
                    end
                    else
                      attr
                  with
                    _ -> attr
              end
              | attr -> attr
            ) attrs
        end


  method register_qname ?(skip=0) qname attr =
    if true(*is_qualified_qname qname*) then begin
      [%debug_log "REGISTER(%d): \"%s\" -> %s"
        (Stack.length stack) qname (iattr_to_str attr)];

      let frame = self#get_frame ~skip attr in
      frame#qadd qname attr
    end


  method register_qname_at_class ?(outer=0) qname attr =
    [%debug_log "REGISTER(%d): \"%s\" -> %s" (Stack.length stack) qname (iattr_to_str attr)];
    let frame = self#find_frame ~outer is_class_frame in
    frame#qadd qname attr


  method register_global_qname qname attr =
    if is_qualified_qname qname then begin
      [%debug_log "REGISTER(%d): \"%s\" -> %s"
        (Stack.length stack) qname (iattr_to_str attr)];

      let frame = self#get_global_frame in
      frame#qadd qname attr
    end


  method lookup_qname ?(afilt=(fun _ -> true)) qname =
    [%debug_log "LOOKUP(%d): \"%s\"" (Stack.length stack) qname];
    try
      Stack.iter
        (fun frame ->
          (*[%debug_log "%s" frame#to_string];*)
          try
            let attrs = frame#qfind_all qname in
            let filtered = List.filter afilt attrs in
            if filtered <> [] then
              raise (Attrs_found filtered)
          with
            Not_found -> ()
        ) stack;
      raise Not_found
    with
      Attrs_found attrs ->
        [%debug_log "FOUND: %s -> [%s]" qname (Xlist.to_string iattr_to_str ";" attrs)];
        attrs

  method lookup_global_qname qname =
    let attrs = global_frame#qfind_all qname in
    [%debug_log "FOUND: %s -> [%s]" qname (Xlist.to_string iattr_to_str ";" attrs)];
    attrs

  method get_naive_fqn name =
    let qn = P.name_to_simple_string name in
    try
      let _ = classtbl#get_package_name qn in
      qn
    with
      _ ->
        let _, id = leftmost_of_name name in
        let fqn =
          try
            let lfqn = classtbl#resolve id in
            let prefix, _ = decompose_qname lfqn in
            prefix^"."^qn
          with
            _ -> qn
        in
        fqn

  method surrounding_class_names =
    let l = ref [] in
    Stack.iter
      (fun frame ->
        try
          l := frame#get_class_name :: !l
        with
          Not_found -> ()
      ) stack;
    !l

  method surrounding_class_has_super =
    let b =
      try
        Stack.iter
          (fun frame ->
            match frame#kind with
            | FKclass(_, has_super) when !has_super -> raise (Frame_found frame)
            | _ -> ()
          ) stack;
        false
      with
        Frame_found _ -> true
    in
    [%debug_log "b=%B" b];
    b

  method surrounding_method_is_static =
    let b =
      try
        Stack.iter
          (fun frame ->
            match frame#kind with
            | FKmethod(_, is_static) when !is_static -> raise (Frame_found frame)
            | _ -> ()
          ) stack;
        false
      with
        Frame_found _ -> true
    in
    [%debug_log "b=%B" b];
    b

  method inner_most_class ?(exclude_current=false) () =
    [%debug_log "exclude_current=%B" exclude_current];
    let s =
      if exclude_current then
        Stack.copy stack
      else
        stack
    in
    if exclude_current then
      ignore (Stack.pop s);
    try
      Stack.iter
        (fun frame ->
          match frame#kind with
          | FKclass(cn, _) -> raise (Attrs_found [IAclass cn])
          | _ -> ()
          (*frame#iter
            (fun id a ->
              match a with
              | IAclass s | IAinterface s -> raise (Attrs_found [a])
              | _ -> ()
            )*)
        ) s;
      raise Not_found
    with
      Attrs_found [a] -> a


  method resolve ?(force_defer=false) name =
    let ss = P.name_to_simple_string name in
    [%debug_log "resolving \"%s\" force_defer=%B" ss force_defer];
    let res =
      if is_simple name then begin
        try
          let afilt = function
            | IAclass _ | IAinterface _ | IAtypename _
            | IAtypeparameter
              -> true
            | _ -> false
          in
          let attrs = self#lookup_identifier ~afilt ss in
          let res =
            match List.nth attrs 0 with
            | IAclass s | IAinterface s | IAtypename s -> s
            | IAtypeparameter -> rightmost_identifier name
            | _ -> assert false
          in
          [%debug_log "resolved: %s --> %s" ss res];
          if force_defer then
            raise Not_found
          else
            R_resolved res
        with
          Not_found ->
            let frms = self#copy_current_stack in
            try
              let res = classtbl#resolve ss in
              R_deferred(ss, frms, res)
            with
              Not_found -> R_deferred(ss, frms, "")
      end
      else begin (* qualified name: unresolved inner class or FQN *)
        let qname = ss in
        try
          let res = classtbl#resolve_qualified_type_name qname in
          [%debug_log "resolved: %s --> %s" qname res];
          if force_defer then
            raise Not_found
          else
            R_resolved res
        with
          Not_found ->
            let s = replace_dot_with_dollar ss in
            let frms = self#copy_current_stack in
            try
              let res = classtbl#resolve s in
              R_deferred(s, frms, res)
            with
              Not_found -> R_deferred(ss, frms, "")
      end
    in
    [%debug_log "\"%s\" -> \"%s\"" ss (resolve_result_to_str res)];
    res
  (* method resolve *)

  method finalize_name_attribute nattr_ref =
    [%debug_log "nattr=%s" (P.name_attribute_to_string !nattr_ref)];
    let rec check_attr ?(continue=true) find_all id = function
      | IAclass s | IAinterface s | IAtypename s as ia -> begin
          let _ = ia in
          [%debug_log "found: %s" (iattr_to_str ia)];
          raise (Type_found (if s = "" then id else s))
      end
      | IAfield as ia -> begin
          let _ = ia in
          [%debug_log "found: %s" (iattr_to_str ia)];
          raise (Expr_found EKfacc)
      end
      | IAarray | IAexpression _ as ia -> begin
          let _ = ia in
          [%debug_log "found: %s" (iattr_to_str ia)];
          nattr_ref := NAexpression EKunknown;
          raise Not_found
      end
      | IAstatic s as ia -> begin
          let _ = ia in
          [%debug_log "found: %s" (iattr_to_str ia)];
          raise (Static_found (if s = "" then id else s))
      end
      | _ when not continue -> ()
      | ia -> begin
          let _ = ia in
          [%debug_log "%s" (iattr_to_str ia)];
          let attrs = find_all id in
          [%debug_log "finding all: %s -> [%s]" id (Xlist.to_string iattr_to_str ";" attrs)];
          List.iter (check_attr ~continue:false find_all id) (List.tl attrs);
          raise Not_found
      end
    in
    try
      let a =
        match !nattr_ref with
        | NAtype rr -> begin
            let ln = self#finalize_resolve_result rr in
            [%debug_log "TYPE(%s)" ln];
            NAtype (R_resolved ln)
        end
        | NAambiguous (R_resolved s) -> begin
            let _ = s in
            [%debug_log "NAambiguous (R_resolved %s)" s];
            raise Not_found
        end
        | NAambiguous (R_deferred(id, frames, cand)) -> begin
            let _ = cand in
            [%debug_log "id=%s cand=%s" id cand];
            if self#partial_typename_resolution_flag then
              raise Not_found;
            try
              Stack.iter
                (fun frame ->
                  [%debug_log "%s" frame#to_string];
                  try
                    check_attr frame#find_all id (frame#find id)
                  with
                    Not_found ->
                      try
                        check_attr frame#qfind_all id (frame#qfind id)
                      with
                        Not_found ->
                          try
                            let id_ = replace_dollar_with_dot id in
                            if id_ <> id then
                              check_attr frame#qfind_all id_ (frame#qfind id_)
                          with
                            Not_found -> ()
                ) frames;
              !nattr_ref
            with
            | Type_found s -> NAtype (R_resolved s)
            | Expr_found ek -> NAexpression ek
            | Static_found s -> NAstatic (R_resolved s)
        end
        | _ -> raise Not_found
      in
      nattr_ref := a
    with
      Not_found -> ()



  method finalize_resolve_result = function
    | R_resolved s -> s
    | R_deferred(id, frames, cand) ->
        [%debug_log "id=\"%s\" cand=\"%s\"" id cand];
        let _resolve_lname lname =
          [%debug_log "\"%s\"" lname];
          try
            Stack.iter
              (fun frame ->
                try
                  match frame#find lname with
                  | IAclass s | IAinterface s | IAtypename s ->
                      raise (Type_found s)
                  | _ -> ()
                with
                  Not_found -> ()
              ) frames;
            raise Not_found
          with
          | Type_found s -> s
          | Not_found ->
              if cand <> "" then
                cand
              else
                classtbl#resolve lname
        in
        let resolve_lname lname =
          try
            _resolve_lname lname
          with
            Not_found ->
              if is_inner lname then begin
                let parent, rest = split_inner lname in
                [%debug_log "parent=\"%s\", rest=\"%s\"" parent rest];
                (_resolve_lname parent)^rest
              end
              else
                raise Not_found
        in
        try
          if cand = "" && String.contains id '.' then begin
            try
              classtbl#resolve_qualified_type_name id
            with
            | Not_found ->
                let s = replace_dot_with_dollar id in
                resolve_lname s
          end
          else
            resolve_lname id
        with
          Not_found ->
            (*warning_msg "name not resolved: %s" id;*)
            (*sprintf "/*[unresolved]*/%s" id*)
            id
  (* method finalize_resolve_result *)

  method reclassify_identifier (attr, ident) =
    [%debug_log "attr=%s ident=%s" (P.name_attribute_to_string !attr) ident];
    if self#in_method then begin
      match !attr with
      | NAexpression ek -> begin
        let afilt = function
          | IAvariable -> true
          | _ -> false
        in
        try
          let _ = self#lookup_identifier ~afilt ident in
          ()
        with
          Not_found -> self#register_qname_at_class ident (IAexpression ek)
      end
      | _ -> ()
    end;
    let check2() =
      [%debug_log "checking..."];
      try (* not yet (only class names are resolved) *)
        let fqn = classtbl#resolve ident in
        NAtype (R_deferred(ident, self#copy_current_stack, fqn))
      with
        Not_found ->
          (* lookup_name ident *)
          NAunknown (* NApackage *)
    in
    let check1() =
      [%debug_log "checking..."];
      try
        let afilt = function
          | IAvariable | IAparameter | IAfield
          | IAclass _ | IAinterface _ | IAtypename _
          | IAstatic _
          | IAtypeparameter
            -> true
          | _ -> false
        in
        let attrs = self#lookup_identifier ~afilt ident in
        match List.nth attrs 0 with
        | IAvariable | IAparameter -> NAexpression EKname

        | IAfield -> NAexpression EKfacc

        | IAstatic s -> NAstatic (R_resolved (if s = "" then ident else s))

        | IAclass s | IAinterface s | IAtypename s -> begin
            NAtype (R_deferred(ident, self#copy_current_stack, s))
        end
        | IAtypeparameter -> NAtype (R_resolved ident)
        | _ -> assert false
      with
        Not_found -> check2()
    in
    let a = check1() in
    if a <> NAunknown then
      attr := a

  method get_package_name name = (* package or normal type or nested type *)
    let qname = P.name_to_simple_string name in
    [%debug_log "qname=%s name=%s" qname (P.name_to_string name)];

    if classtbl#is_package qname then begin
      set_name_attribute NApackage name;
      [%debug_log "pname=%s" (P.name_to_string name)];
      qname
    end
    else begin
      try
        let prefix_name, base = decompose_name name in
        let prefix = P.name_to_simple_string prefix_name in
        [%debug_log "prefix=%s" prefix];
        let spath = self#classtbl#get_source_dir#path in
        let ppath = Filename.concat spath (pkg_to_path prefix) in
        let _path = Filename.concat ppath base in

        [%debug_log "spath=%s" spath];
        [%debug_log "ppath=%s" ppath];
        [%debug_log "_path=%s" _path];

        if
          not self#no_implicit_name_resolution_flag &&
          self#current_source#tree#is_dir ppath
        then begin

          if not (classtbl#is_package prefix) then begin
            classtbl#add_package ~dir:(self#current_source#tree#get_entry ppath) prefix;
          end;
          set_name_attribute NApackage prefix_name;

          if self#current_source#tree#is_dir _path then begin
            classtbl#add_package ~dir:(self#current_source#tree#get_entry _path) qname;
            set_name_attribute NApackage name;
            [%debug_log "pname=%s" (P.name_to_string name)];
            qname
          end
          else begin
            [%debug_log "pname=%s" (P.name_to_string prefix_name)];
            prefix
          end

        end
        else if classtbl#is_package prefix then begin
          set_name_attribute NApackage prefix_name;
          [%debug_log "pname=%s" (P.name_to_string prefix_name)];
          prefix
        end
        else
          (*classtbl#get_package_name *)prefix

      with
        _ -> failwith "Parser_aux.env#get_package_name"
    end

  method resolve_qualified_type_name name =
    let qname = P.name_to_simple_string name in
    classtbl#_resolve_qualified_type_name (self#get_package_name name) qname

  method set_attribute_A ?(force_defer=false) name =
    let rec set n =
      match n.n_desc with
      | Nsimple(at, _) -> set1 at (NAambiguous (self#resolve ~force_defer n))
      | Nqualified(at0, n0, _, _) -> set n0; set1 at0 (NAambiguous (self#resolve ~force_defer n))
      | _ -> ()
    in
    set name

  method! init =
    [%debug_log "called"];
    global_frame <- new frame FKother;
    super#init;
    Stack.clear stack;
    self#begin_scope ~frame_opt:(Some global_frame) ();
    self#reset_java_lang_spec;
    self#reset_actual_java_lang_spec;
    Stack.clear context_stack;
    Stack.push (C_toplevel (create_top_stat())) context_stack

  initializer
    self#init

end (* of class Parser_aux.env *)
]


let ty_list_union tyl0 tyl1 =
  let get_rep = P.type_to_string in
  let a0 = List.map (fun ty -> get_rep ty, ty) tyl0 in
  let a1 = List.map (fun ty -> get_rep ty, ty) tyl1 in
  let d0, _ = List.split a0 in
  let d1, _ = List.split a1 in
  let u = Xlist.union d0 d1 in
  List.map (fun x -> try List.assoc x a0 with Not_found -> List.assoc x a1) u


module type STATE_T = sig
  val env      : env
end


let lexing_pos_start = Langs_common.Position.lexing_pos_start
let lexing_pos_end = Langs_common.Position.lexing_pos_end
let get_lc = Langs_common.Position.get_lc


[%%capture_path
module F (Stat : STATE_T) = struct

  open Stat

  let get_range start_pos end_pos =
    let start_line, start_char = get_lc start_pos in
    let end_line, end_char = get_lc end_pos in
    let start_offset = start_pos.Lexing.pos_cnum in
    let end_offset = end_pos.Lexing.pos_cnum in
    (start_line, start_char), (end_line, end_char), start_offset, end_offset

  let get_loc start_pos end_pos = Astloc.of_lexposs start_pos end_pos

  let parse_error (*start_pos*)_ end_pos msg =
    let line, char = get_lc end_pos in
    let head = sprintf "[%d:%d]" line char in
    fail_to_parse ~head msg

  let parse_error_loc loc (fmt : ('a, unit, string, 'b) format4) : 'a =
    let head = sprintf "[%s]" (Loc.to_string loc) in
    Printf.ksprintf (fail_to_parse ~head) fmt

  let parse_warning start_pos end_pos =
    let loc = get_loc start_pos end_pos in
    warning_loc loc

  let get_loc_for_lex lexbuf =
    let get_range lexbuf =
      let start_pos = lexing_pos_start lexbuf in
      let end_pos = lexing_pos_end lexbuf in
      let start_line, start_char = get_lc start_pos in
      let end_line, end_char = get_lc end_pos in
      let start_offset = start_pos.Lexing.pos_cnum in
      let end_offset = end_pos.Lexing.pos_cnum in
      start_pos.Lexing.pos_fname,
      (start_line, start_char),
      (end_line, end_char),
      start_offset, end_offset
    in
    let fname, (sl, sc), (el, ec), so, eo = get_range lexbuf in
    let loc = Loc.make ~fname so eo sl sc el ec in
    loc


  let register_identifier_as_class fqn id     = env#register_identifier ~qualify:true id (IAclass fqn)
  let register_identifier_as_interface fqn id = env#register_identifier ~qualify:true id (IAinterface fqn)
  let register_identifier_as_typename fqn id  = env#register_identifier id (IAtypename fqn)
  let register_identifier_as_method id        = env#register_identifier id IAmethod
  let register_identifier_as_parameter id _   = env#register_identifier id IAparameter
  let register_identifier_as_variable id _    = env#register_identifier id IAvariable

  let register_identifier_as_field ?(is_static=false) id _ =
    let attr =
      if is_static then
        IAstatic ""
      else
        IAfield
    in
    env#register_identifier id attr

  let register_identifier_as_constructor id   = env#register_identifier id IAconstructor
  let register_identifier_as_label id         = env#register_identifier id IAlabel
  let register_identifier_as_typeparameter id = env#register_identifier id IAtypeparameter

  let register_identifier_as_static_member fqn id =
    env#register_identifier id (IAstatic fqn)

  let register_identifier_as_enumconst fqn id =
    env#register_identifier ~skip:1 id (IAstatic fqn)

  let register_qname ?(skip=0) n a =
    let ss = P.name_to_simple_string n in
    [%debug_log "\"%s\"" ss];
    try
      let _, id = leftmost_of_name n in
      (*if env#no_implicit_name_resolution_flag then
        env#register_qname ~skip ss a
      else *)if env#classtbl#is_resolvable id then
        env#register_global_qname ss a
      else
        env#register_qname ~skip ss a
    with
      _ -> ()

  let register_qname_as_class n         = register_qname n (IAclass "")
  let register_qname_as_interface n     = register_qname n (IAinterface "")

  let register_qname_as_typename ?(skip=0) n =
    register_qname ?skip:(Some skip) n (IAtypename "")

  let register_qname_as_typename_at_class ?(outer=0) n =
    let ss = P.name_to_simple_string n in
    [%debug_log "\"%s\"" ss];
    env#register_qname_at_class ~outer ss (IAtypename "")

  let register_qname_as_method n        = register_qname n IAmethod
  let register_qname_as_static_member n = register_qname n (IAstatic "")
  let register_qname_as_parameter n     = register_qname n IAparameter
  let register_qname_as_variable n      = register_qname n IAvariable
  let register_qname_as_field n         = register_qname n IAfield
  let register_qname_as_constructor n   = register_qname n IAconstructor
  let register_qname_as_label n         = register_qname n IAlabel
  let register_qname_as_typeparameter n = register_qname n IAtypeparameter
  let register_qname_as_expression n    = register_qname n (IAexpression EKunknown)
  let register_qname_as_array n         = register_qname n IAarray


  let _mkty loc d = { ty_desc=d; ty_loc=loc }
  let _mktyargs loc tyargs = { tas_type_arguments=tyargs; tas_loc=loc }
  let mktyparams sp ep typarams = { tps_type_parameters=typarams; tps_loc=(get_loc sp ep) }
  let _mktype loc d = { ty_desc=d; ty_loc=loc }
  let _mkmod loc d = { m_desc=d; m_loc=loc }
  let annot_to_mod a = _mkmod a.a_loc (Mannotation a)
  let annots_to_mods = List.map annot_to_mod
  let _mkexpr loc d = { e_desc=d; e_loc=loc }

  let _mkannot loc d = { a_desc=d; a_loc=loc }
  let name_to_ty a n = _mkty n.n_loc (TclassOrInterface [TSname(a, n)])
  let name_to_ty_args loc a n args = _mkty loc (TclassOrInterface [TSapply(a, n, args)])

  let add_ann _ a { ty_desc=d; ty_loc=loc } =
    match d with
    | Tprimitive(a0, pt) -> begin
        _mkty loc (Tprimitive(a@a0, pt))
    end
    | TclassOrInterface (spec::tl) -> begin
        let spec' =
          match spec with
          | TSname(a0, n)        -> TSname(a@a0, n)
          | TSapply(a0, n, args) -> TSapply(a@a0, n, args)
        in
        _mkty loc (TclassOrInterface(spec'::tl))
    end
    | _ -> assert false

  let _simple_name_to_prim loc n = _mkprim loc (Pname n)
  let _simple_name_to_expr loc n = _mkexpr loc (Eprimary (_simple_name_to_prim loc n))
  let mkpkgdecl loc a n = { pd_annotations=a; pd_name=n; pd_loc=loc }
  let _mkcbd loc d = { cbd_desc=d; cbd_loc=loc }
  let _mkrbd loc d = { rbd_desc=d; rbd_loc=loc }
  let mkfd loc ms ty vds = { fd_modifiers=ms;
                             fd_type=ty;
                             fd_variable_declarators=vds;
                             fd_loc=loc;
                           }

  let mkec loc annots id args cb = { ec_annotations=annots;
                                     ec_identifier=id;
                                     ec_arguments=args;
                                     ec_class_body=cb;
                                     ec_loc=loc
                                   }

  let mkfp ?(receiver=None) loc ms ty vdid va =
    { fp_modifiers=ms;
      fp_type=ty;
      fp_variable_declarator_id=vdid;
      fp_variable_arity=va;
      fp_loc=loc;
      fp_receiver=receiver;
    }
  let _mkargs loc args = { as_arguments=args; as_loc=loc }
  let _mkatmd loc d = { atmd_desc=d; atmd_loc=loc }
  let _mkimd loc d = { imd_desc=d; imd_loc=loc }
  let _mkch loc ms id id_loc ts_opt s_opt i_opt p_opt =
    { ch_modifiers=ms;
      ch_identifier=id;
      ch_identifier_loc=id_loc;
      ch_type_parameters=ts_opt;
      ch_extends_class=s_opt;
      ch_implements=i_opt;
      ch_permits=p_opt;
      ch_loc=loc;
    }
  let _mkrh loc ms id id_loc ts_opt h i_opt =
    { rh_modifiers=ms;
      rh_identifier=id;
      rh_identifier_loc=id_loc;
      rh_type_parameters=ts_opt;
      rh_record_header=h;
      rh_implements=i_opt;
      rh_loc=loc;
    }
  let _mkmodule loc h b = { mod_head=h; mod_body=b; mod_loc=loc }
  let _mkmn loc n = { mn_name=n; mn_loc = loc }
  let _mkmdh loc a o n = { mdh_annotations=a; mdh_open=o; mdh_name=n; mdh_loc=loc }
  let _mkmb loc ds = { mb_module_directives=ds; mb_loc=loc }
  let _mkmd loc d = { md_desc=d; md_loc=loc }
  let _mkcd loc d = { cd_desc=d; cd_loc=loc }
  let _mkifh loc ms id ts_opt s_opt p_opt = { ifh_modifiers=ms;
                                              ifh_identifier=id;
                                              ifh_type_parameters=ts_opt;
                                              ifh_extends_interfaces=s_opt;
                                              ifh_permits=p_opt;
                                              ifh_loc=loc;
                                            }
  let _mkifd loc d = { ifd_desc=d; ifd_loc=loc }
  let mkmh loc m tp al rt (id_loc, id) pl p d t =
    { mh_modifiers=m;
      mh_type_parameters=tp;
      mh_annotations=al;
      mh_return_type=rt;
      mh_name=id;
      mh_name_loc=id_loc;
      mh_parameters_loc=pl;
      mh_parameters=p;
      mh_dims=d;
      mh_throws=t;
      mh_loc=loc
    }
  let mkimed loc mh b = { amd_method_header=mh; amd_body=b; amd_loc=loc }
  let mkcnd loc m tp n pl p t b = { cnd_modifiers=m;
                                    cnd_type_parameters=tp;
                                    cnd_name=n;
                                    cnd_parameters_loc=pl;
                                    cnd_parameters=p;
                                    cnd_throws=t;
                                    cnd_body=b;
                                    cnd_loc=loc
                                  }
  let mkccnd sp ep m i b = { ccnd_modifiers=m;
                             ccnd_name=i;
                             ccnd_body=b;
                             ccnd_loc=(get_loc sp ep);
                           }


  let _mkfqn ?(exclude_current=false) sep id =
    let add_pkg_name s =
      let pname = env#current_package_name in
      if pname = "" then
        s
      else
        pname^"."^s
    in
    let fqn =
      try
        match env#inner_most_class ~exclude_current () with
        | IAclass s | IAinterface s | IAtypename s -> add_pkg_name (s^sep^id)
        | _ -> raise Not_found
      with
        Not_found -> add_pkg_name id
    in
    [%debug_log "\"%s\" -> \"%s\"" id fqn];
    fqn

  let mkfqn ?(exclude_current=false) = _mkfqn ~exclude_current "."

  let mkfqn_cls ?(exclude_current=false) = _mkfqn ~exclude_current "$"


  let is_local_name ?(force=false) n =
    [%debug_log "\"%s\" (force=%B)" (P.name_to_simple_string n) force];
    let b =
      if is_qualified n then begin
        false
      end
      else if not force && env#partial_name_resolution_flag then begin
        false
      end
      else begin
        let is_local n =
          let id = rightmost_identifier n in
          try
            let attrs = env#lookup_identifier id in
            let rec iter = function
              | [] -> false
              | (IAfield | IAstatic _)::_ -> false
              | (IAvariable | IAparameter)::_ -> true
              | (IAexpression _ | IAarray)::rest -> iter rest
              | _ -> false
            in
            iter attrs
          with
            Not_found -> false
        in
        is_local n
      end
    in
    [%debug_log "\"%s\" --> %B" (P.name_to_simple_string n) b];
    b

  let is_implicit_field_name n =
    [%debug_log "\"%s\"" (P.name_to_simple_string n)];
    let b =
      if is_qualified n then begin
        false
      end
      else begin
        let id = rightmost_identifier n in
        try
          let attrs = env#lookup_identifier id in
          let rec iter = function
            | [] -> raise Not_found
            | IAfield::_ -> true
            | (IAexpression _ | IAarray | IAmethod)::rest -> iter rest
            | _ -> false
          in
          iter attrs
        with
          Not_found -> (*not (env#classtbl#is_resolvable id)*)false
      end
    in
    [%debug_log "\"%s\" --> %B" (P.name_to_simple_string n) b];
    b

  let get_type_fqn n =
    (*if env#no_implicit_name_resolution_flag then
      P.name_to_simple_string n
    else *)begin
    [%debug_log "\"%s\"" (P.name_to_simple_string n)];
    let doit n =
      if is_qualified n then begin
        let fqn = env#get_naive_fqn n in
        try
          env#classtbl#resolve_qualified_type_name fqn
        with
          _ -> begin
            [%debug_log "\"%s\" --> unknown" fqn];
            raise (Unknown fqn)
          end
      end
      else begin (* not (is_qualified n) *)
        let id = rightmost_identifier n in
        try
          let attrs = env#lookup_identifier id in
          [%debug_log "FOUND: %s -> [%s]" id (Xlist.to_string iattr_to_str ";" attrs)];
(*
          begin
            try
              List.iter
                (fun a ->
                  match a with
                  | IAclass s | IAinterface s | IAtypename s -> raise (Type_found s)
                  | IAtypeparameter -> raise (Type_found id)
                  | _ -> ()
                ) "" attrs;
              raise Not_found
            with
              Type_found s -> s
          end
*)
          let doit i =
            match List.nth attrs i with
            | IAclass s | IAinterface s | IAtypename s -> s
            | IAtypeparameter -> id
            | _ -> raise Not_found
          in
          doit 0
        with
          Not_found -> begin
            try
              env#classtbl#resolve id
            with
              Not_found -> begin
                try
                  let s_path = env#classtbl#get_source_dir#path in
                  let path = Filename.concat s_path (id^".java") in
                  if env#current_source#tree#exists path then
                    id
                  else
                    raise Not_found
                with
                  Not_found ->
                    try
                      env#classtbl#resolve id
                    with
                      Not_found ->
                        [%debug_log "\"%s\" --> unknown" id];
                        raise (Unknown id)
              end
          end
      end
    in
    let fqn = doit n in
    [%debug_log "\"%s\" --> %s" (P.name_to_simple_string n) fqn];
    fqn
    end
  (* func get_type_fqn *)

  let get_type_name n =
    let ss = P.name_to_simple_string n in
    [%debug_log "\"%s\"" ss];

    let afilt = function
      | IAclass _ | IAinterface _ | IAtypename _ | IAtypeparameter -> true
      | _ -> false
    in
    let get_tyname =
      List.fold_left
        (fun tn a ->
          match a with
          | IAclass n | IAinterface n | IAtypename n -> n
          | _ -> tn
        ) ""
    in
    let rec get name =
      match name.n_desc with
      | Nsimple(_, i) -> begin
          try
            get_tyname (env#lookup_identifier ~afilt i)
          with
            Not_found ->
              try
                let tn = get_tyname (env#lookup_qname ~afilt ss) in
                if tn = "" then
                  try
                    env#classtbl#resolve i
                  with
                    Not_found -> i
                else
                  tn
              with
                Not_found -> env#classtbl#resolve i
      end
      | Nqualified(_, n, _, i) -> begin
          (*try
            get_tyname (env#lookup_identifier ~afilt i)
          with
            Not_found ->*)
              let ss = P.name_to_simple_string name in
              let tn = get_tyname (env#lookup_qname ~afilt ss) in
              if tn = "" then
                try
                  let pt = get n in
                  if pt = "" then
                    ss
                  else
                    pt^"$"^i
                with
                  Not_found -> ss
              else
                tn
      end
      | Nerror s -> s
    in
    let tyname = get n in
    [%debug_log "%s --> \"%s\"" ss tyname];
    tyname

  let is_type_name n =
    let b =
      try
        let _ = get_type_name n in
        true
      with
        Not_found -> false
    in
    [%debug_log "%s --> %B" (P.name_to_simple_string n) b];
    b

  let is_static_member n =
    let ss = P.name_to_simple_string n in
    [%debug_log "\"%s\"" ss];
    let afilt = function
      | IAstatic _ -> true
      | _ -> false
    in
    let b =
      if is_qualified n then
        try
          let _ = env#lookup_qname ~afilt ss in
          true
        with
          Not_found -> false
      else
        try
          let attrs = env#lookup_identifier ss in
          let rec iter = function
            | [] -> false
            | IAstatic _::_ -> true
            | _ -> false
          in
          iter attrs
        with
          Not_found -> false
    in
    [%debug_log "%s --> %B" (P.name_to_string n) b];
    b

  let is_expr_name n =
    let ss = P.name_to_simple_string n in
    [%debug_log "\"%s\"" ss];
    let afilt = function
      | IAexpression _ -> true
      | _ -> false
    in
    let b =
      try
        let _ = env#lookup_qname ~afilt ss in
        true
      with
        Not_found -> false
    in
    [%debug_log "%s --> %B" (P.name_to_string n) b];
    b

  let is_field_access n =
    [%debug_log "\"%s\"" (P.name_to_simple_string n)];
    let b =
      if is_qualified n then begin
        let nattr, id = leftmost_of_name n in
        is_expr_attr !nattr ||
        let afilt = function
          | IAfield | IAstatic _ | IAvariable | IAparameter -> true
          | _ -> false
        in
        try
          let _ = env#lookup_identifier ~afilt id in
          true
        with
          Not_found ->
            let afilt = function
              | IAclass _ | IAinterface _ | IAtypename _ -> true
              | _ -> false
            in
            try
              let _ = env#lookup_identifier ~afilt id in
              false
            with
              Not_found ->
                (*not (env#classtbl#is_resolvable id)*)
                false
      end
      else begin
        let id = rightmost_identifier n in
        let afilt = function
          | IAfield -> true
          | _ -> false
        in
        try
          let _ = env#lookup_identifier ~afilt id in
          true
        with
          Not_found -> false
      end
    in
    (*Printf.printf "\"%s\" -> %B\n%!" (P.name_to_string n) b;*)
    [%debug_log "\"%s\" --> %B" (P.name_to_simple_string n) b];
    b



  let mkty sp ep d = _mkty (get_loc sp ep) d
  let mkwb sp ep d = { wb_desc=d; wb_loc=(get_loc sp ep) }
  let _mktyarg loc d = { ta_desc=d; ta_loc=loc }
  let mktyarg sp ep d = _mktyarg (get_loc sp ep) d
  let mktyparam sp ep (al, tvar) tb = { tp_type_variable=tvar;
                                        tp_annotations=al;
                                        tp_type_bound=tb;
                                        tp_loc=(get_loc sp ep);
                                      }
  let _mktb loc rty ab = { tb_reference_type=rty;
                            tb_additional_bounds=ab;
                            tb_loc=loc;
                          }
  let mktb sp ep rty ab = _mktb (get_loc sp ep) rty ab
  let mkab sp ep intf = { ab_interface=intf; ab_loc=(get_loc sp ep) }

  let _mkname loc d = { n_desc=d; n_loc=loc }
  let mkname sp ep d = _mkname (get_loc sp ep) d

  let mkerrname sp ep s =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    if env#keep_going_flag then
      { n_desc=Nerror s; n_loc=loc }
    else
      parse_error_loc loc "syntax error: %s" s

  let mktyargs sp ep d = _mktyargs (get_loc sp ep) d
  let mktype sp ep d = _mktype (get_loc sp ep) d
  let mkmod sp ep d = _mkmod (get_loc sp ep) d
  let mkerrmod sp ep s =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    if env#keep_going_flag then
      { m_desc=Merror s; m_loc=loc }
    else
      parse_error_loc loc "syntax error: %s" s

  let mkmods sp ep ms = { ms_modifiers=ms; ms_loc=(get_loc sp ep) }
  let mkaop sp ep d = { ao_desc=d; ao_loc=(get_loc sp ep) }
  let mkstmt ?(esp=Lexing.dummy_pos) ?(eep=Lexing.dummy_pos) sp ep d = {
    s_desc=d;
    s_loc=(get_loc sp ep);
    s_extra_loc=(
    if esp != Lexing.dummy_pos && eep != Lexing.dummy_pos then
      Some (get_loc esp eep)
    else
      None
   )
  }
  let mkerrstmt sp ep s =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    if env#keep_going_flag then
      { s_desc=Serror s; s_loc=loc; s_extra_loc=None }
    else
      parse_error_loc loc "syntax error: %s" s

  let mkexpr sp ep d = _mkexpr (get_loc sp ep) d

  let mklp sp ep d = { lp_desc=d; lp_loc=(get_loc sp ep) }

  let mkerrexpr sp ep s =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    if env#keep_going_flag then
      { e_desc=Eerror s; e_loc=loc }
    else
      parse_error_loc loc "syntax error: %s" s

  let mkstmtexpr sp ep d = { se_desc=d; se_loc=(get_loc sp ep) }

  let mkerrstmtexpr sp ep s =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    if env#keep_going_flag then
      { se_desc=SEerror s; se_loc=loc }
    else
      parse_error_loc loc "syntax error: %s" s

  let mkprim sp ep d = _mkprim (get_loc sp ep) d

  let mkerrprim sp ep s =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    if env#keep_going_flag then
      { p_desc=Perror s; p_loc=loc }
    else
      parse_error_loc loc "syntax error: %s" s

  let mkannot sp ep d = _mkannot (get_loc sp ep) d
  let mkev sp ep d = { ev_desc=d; ev_loc=(get_loc sp ep) }
  let simple_name_to_prim sp ep n = _simple_name_to_prim (get_loc sp ep) n

  let rec name_to_facc name =
    [%debug_log "%s" (P.name_to_string name)];
    match name.n_desc with
    | Nsimple(a, i) -> begin
        [%debug_log "a=%s i=%s" (name_attribute_to_string !a) i];
        let lab =
          match !a with
          | NAexpression EKname | NAstatic _ -> Pname name
          | NAexpression EKfacc -> PfieldAccess(FAimplicit name)
          | _ -> begin
              try
                if List.mem IAfield (env#lookup_identifier i) then begin
                  a := NAexpression EKfacc;
                  PfieldAccess(FAimplicit name)
                end
                else begin
                  a := NAexpression EKname;
                  Pname name
                end
              with
                Not_found -> begin
                  a := NAambiguous (env#resolve name);
                  PfieldAccess(FAimplicit name)
                end
          end
        in
        _mkprim name.n_loc lab
    end
    | Nqualified(a, n, [], i) -> begin
        a := NAexpression EKfacc;
        _mkprim name.n_loc (PfieldAccess(FAprimary(name_to_facc n, i)))
    end
    | Nqualified(_, _, _, _) -> _mkprim name.n_loc (Pname name)

    | Nerror _ -> _mkprim name.n_loc (Pname name)

  let _name_to_prim ?(whole=true) loc n =
    [%debug_log "[%s] %s (whole=%B)" (Loc.to_string loc) (P.name_to_string n) whole];

    if
      env#partial_name_resolution_flag &&
      try
        let q = get_qualifier n in
        is_local_name ~force:true (leftmost_name q)
      with _ -> false
    then begin
      [%debug_log "@"];
      name_to_facc n
    end
    else if
      env#partial_name_resolution_flag &&
      not (is_simple n && is_local_name ~force:true n)
    then begin
      set_name_attribute ~force:true (NAambiguous (mkresolved (P.name_to_simple_string n))) n;
      [%debug_log "[%s] %s" (Loc.to_string loc) (P.name_to_string n)];
      _mkprim loc (Pname n)
    end
    else

    let id = rightmost_identifier n in
    try
      let q = get_qualifier n in
      [%debug_log "q=%s" (P.name_to_string q)];
      let q_is_tyname, q_tyname =
        try
          let tn = get_type_name q in
          true, tn
        with
          Not_found -> false, ""
      in
      [%debug_log "q_tyname=\"%s\"" q_tyname];
      if not env#partial_typename_resolution_flag && q_is_tyname then begin
        set_name_attribute (NAtype (R_resolved q_tyname)) q;
        let na = NAambiguous (env#resolve ~force_defer:true n) in
        [%debug_log "na=%s" (P.name_attribute_to_string na)];
        set_name_attribute ~force:true na n;
        [%debug_log "n=%s" (P.name_to_string n)];
        _mkprim loc (Pname n)
      end
      else if is_expression q then begin
        name_to_facc n
      end
      else if is_field_access n then begin
        name_to_facc n
      end
      else if
        whole && is_simple q &&
        not (is_leftmost_id_capitalized q) &&
        (
         env#in_static_method ||
         (env#rely_on_naming_convention_flag && is_rightmost_id_capitalized q) ||
         (not env#rely_on_naming_convention_flag && (not env#surrounding_class_has_super))
        )
      then begin
        set_name_attribute (NAtype (env#resolve q)) q;
        [%debug_log "[%s] %s" (Loc.to_string loc) (P.name_to_string n)];
        _mkprim loc (Pname n)
      end
      else begin
        if whole then
          set_name_attribute (NAambiguous (env#resolve q)) q
        else
          set_name_attribute ~force:true (NAambiguous (env#resolve ~force_defer:true n)) n;
        [%debug_log "[%s] %s" (Loc.to_string loc) (P.name_to_string n)];
        _mkprim loc (Pname n)
      end
    with
      Not_found -> begin (* n is a simple name *)
        if is_field_access n then begin
          name_to_facc n
        end
        else
          try
            let rec iter = function
              | [] -> begin
                  set_name_attribute (NAexpression EKfacc) n;
                  _mkprim loc (PfieldAccess(FAimplicit n))
              end
              | (IAstatic fqn)::_ -> begin
                  [%debug_log "fqn=\"%s\"" fqn];
                  let fqn = if fqn = "" then id else fqn in
                  set_name_attribute (NAstatic (R_resolved fqn)) n;
                  _mkprim loc (Pname n)
              end
              | IAfield::_ -> begin
                  set_name_attribute (NAexpression EKfacc) n;
                  _mkprim loc (PfieldAccess(FAimplicit n))
              end
              | (IAvariable | IAparameter)::_ -> begin
                  set_name_attribute (NAexpression EKname) n;
                  _mkprim loc (Pname n)
              end
              | _::rest -> iter rest
            in
            iter (env#lookup_identifier id)
          with
            Not_found -> begin
              let na = NAambiguous (env#resolve ~force_defer:true n) in
              [%debug_log "na=%s" (P.name_attribute_to_string na)];
              set_name_attribute na n;
              [%debug_log "[%s] %s" (Loc.to_string loc) (P.name_to_string n)];
              _mkprim loc (PfieldAccess(FAimplicit n))
            end
      end

  let _name_to_expr ?(whole=true) loc n = _mkexpr loc (Eprimary (_name_to_prim ~whole loc n))
  let name_to_prim sp ep n = _name_to_prim (get_loc sp ep) n
  let simple_name_to_expr sp ep n = _simple_name_to_expr (get_loc sp ep) n
  let name_to_expr ?(whole=true) sp ep n = _name_to_expr ~whole (get_loc sp ep) n
  let mkimpdecl sp ep d = { id_desc=d; id_loc=(get_loc sp ep) }
  let mkerrimpdecl sp ep s =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    if env#keep_going_flag then
      { id_desc=IDerror s; id_loc=loc }
    else
      parse_error_loc loc "syntax error: %s" s

  let mkcic sp ep d = { cic_desc=d; cic_loc=(get_loc sp ep) }
  let mkcb sp ep decls = { cb_class_body_declarations=decls; cb_loc=(get_loc sp ep) }
  let mkrb sp ep decls = { rb_record_body_declarations=decls; rb_loc=(get_loc sp ep) }
  let mkcbd sp ep d = _mkcbd (get_loc sp ep) d
  let mkrbd sp ep d = _mkrbd (get_loc sp ep) d
  let mkerrcbd sp ep s =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    if env#keep_going_flag then
      { cbd_desc=CBDerror s; cbd_loc=loc }
    else
      parse_error_loc loc "syntax error: %s" s

  let mksb sp ep sbs srs= { sb_switch_block_stmt_grps=sbs; sb_switch_rules=srs; sb_loc=(get_loc sp ep) }

  let mksrl sp ep x = { srl_desc=x; srl_loc=(get_loc sp ep) }

  let mksrb sp ep x = { srb_desc=x; srb_loc=(get_loc sp ep) }

  let mkexc sp ep c = { exc_class=c; exc_loc=(get_loc sp ep) }
  let mkexi sp ep ifs = { exi_interfaces=ifs; exi_loc=(get_loc sp ep) }
  let mkim sp ep ifs = { im_interfaces=ifs; im_loc=(get_loc sp ep) }
  let mkpm sp ep tns = { pm_type_names=tns; pm_loc=(get_loc sp ep) }
  let mkeb sp ep ecs cbds = { eb_enum_constants=ecs;
                              eb_class_body_declarations=cbds;
                              eb_loc=(get_loc sp ep)
                            }

  let mkabd sp ep decls = { abd_aspect_body_declarations=decls; abd_loc=(get_loc sp ep) }
  let mkdd sp ep d = { dd_desc=d; dd_loc=(get_loc sp ep) }
  let mkpcd sp ep m i pl p pe = { pcd_modifiers=m;
                                  pcd_name=i;
                                  pcd_parameters_loc=pl;
                                  pcd_parameters=p;
                                  pcd_pointcut_expr=pe;
                                  pcd_loc=(get_loc sp ep);
                               }
  let mkpe sp ep d = { pe_desc=d; pe_loc=(get_loc sp ep) }
  let mkcpe sp ep d = { cpe_desc=d; cpe_loc=(get_loc sp ep) }

  let mkvd sp ep vdid vdini =
    { vd_variable_declarator_id=vdid;
      vd_variable_initializer=vdini;
      vd_is_local=(ref true);
      vd_loc=(get_loc sp ep)
    }
  let mkvi sp ep d = { vi_desc=d; vi_loc=(get_loc sp ep) }

  let mkerrvi sp ep s =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    if env#keep_going_flag then
      { vi_desc=VIerror s; vi_loc=loc }
    else
      parse_error_loc loc "syntax error: %s" s

  let mkth sp ep es = { th_exceptions=es; th_loc=(get_loc sp ep) }
  let mkcnb sp ep eci bss = { cnb_explicit_constructor_invocation=eci;
                              cnb_block=bss;
                              cnb_loc=(get_loc sp ep)
                            }
  let mkb sp ep bss = { b_block_statements=bss; b_loc=(get_loc sp ep) }
  let mkeci sp ep d = { eci_desc=d; eci_loc=(get_loc sp ep) }

  let mkerreci sp ep s =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    if env#keep_going_flag then
      { eci_desc=ECIerror s; eci_loc=loc }
    else
      parse_error_loc loc "syntax error: %s" s

  let mkmr sp ep d = { mr_desc=d; mr_loc=(get_loc sp ep) }
  let mkargs sp ep d = _mkargs (get_loc sp ep) d
  let mkib sp ep imds = { ib_member_declarations=imds; ib_loc=(get_loc sp ep) }
  let mkatb sp ep ateds = { atb_member_declarations=ateds; atb_loc=(get_loc sp ep) }
  let mkatmd sp ep d = _mkatmd (get_loc sp ep) d
  let mkimd sp ep d = _mkimd (get_loc sp ep) d
  let mkbs sp ep d = { bs_desc=d; bs_loc=(get_loc sp ep) }
  let mkad ?(ellipsis=false) sp ep a = { ad_annotations=a;
                                         ad_loc=(get_loc sp ep);
                                         ad_ellipsis=ellipsis;
                                       }
  let mkerrbs sp ep s =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    if env#keep_going_flag then
      { bs_desc=BSerror s; bs_loc=loc }
    else
      parse_error_loc loc "syntax error: %s" s


  let mklvd sp ep ms ty vds = { lvd_modifiers=ms;
                                lvd_type=ty;
                                lvd_variable_declarators=vds;
                                lvd_loc=(get_loc sp ep)
                              }
  let mkfi sp ep d = { fi_desc=d; fi_loc=(get_loc sp ep) }
  let mkres sp ep d = { r_desc=d;
                        r_loc=(get_loc sp ep);
                      }
  let mkresspec sp ep rl = { rs_resources=rl; rs_loc=(get_loc sp ep) }
  let mkcfp loc ms tl vdid = { cfp_modifiers=ms;
                               cfp_type_list=tl;
                               cfp_variable_declarator_id=vdid;
                               cfp_loc=loc
                             }
  let mkcatch sp ep param b = { c_formal_parameter=param; c_block=b; c_loc=(get_loc sp ep) }
  let mkfinally sp ep b = { f_block=b; f_loc=(get_loc sp ep)}
  let mkmi sp ep d = { mi_desc=d; mi_loc=(get_loc sp ep) }
  let mktd sp ep d = { td_desc=d; td_loc=(get_loc sp ep) }
  let mkerrtd sp ep s =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    if env#keep_going_flag then
      { td_desc=TDerror s; td_loc=loc }
    else
      parse_error_loc loc "syntax error: %s" s

  let mkaa sp ep d = { aa_desc=d; aa_loc=(get_loc sp ep) }
  let mkch sp ep ms id id_loc ts_opt s_opt i_opt p_opt =
    _mkch (get_loc sp ep) ms id id_loc ts_opt s_opt i_opt p_opt
  let mkrh sp ep ms id id_loc ts_opt h i_opt = _mkrh (get_loc sp ep) ms id id_loc ts_opt h i_opt
  let mkmodule sp ep h b = _mkmodule (get_loc sp ep) h b
  let mkmn sp ep n = _mkmn (get_loc sp ep) n
  let mkmdh sp ep a o n = _mkmdh (get_loc sp ep) a o n
  let mkmb sp ep ds = _mkmb (get_loc sp ep) ds
  let mkmd sp ep d = _mkmd (get_loc sp ep) d
  let mkcd sp ep d = _mkcd (get_loc sp ep) d
  let mkifh sp ep ms id ts_opt s_opt p_opt = _mkifh (get_loc sp ep) ms id ts_opt s_opt p_opt
  let mkifd sp ep d = _mkifd (get_loc sp ep) d
  let mkde sp ep d = { de_desc=d; de_loc=(get_loc sp ep) }
  let mksl sp ep d = { sl_desc=d; sl_loc=(get_loc sp ep) }
  let mkevp sp ep d = { evp_desc=d; evp_loc=(get_loc sp ep) }

  let mkcu p i t = { cu_package=p; cu_imports=i; cu_tydecls=t; cu_modecl=None }
  let mkmcu i m = { cu_package=None; cu_imports=i; cu_tydecls=[]; cu_modecl=(Some m) }

  let begin_scope ?(kind=FKother) () = env#begin_scope ~kind ()
  let end_scope() = env#end_scope()

  let end_typeparameter_scope = function
    | Some ts -> List.iter (fun _ -> end_scope()) ts.tps_type_parameters
    | None -> ()

  let is_predefined_annotation =
    let l =
      [
       "Target";
       "Retention";
       "Inherited";
       "Override";
       "SuppressWarnings";
       "Deprecated";
       "SafeVarargs";
       "Repeatable";
       "FunctionalInterface"
     ]
    in
    let predefined_annotations = Xset.create 0 in
    List.iter (Xset.add predefined_annotations) l;
    fun a ->
      match a.a_desc with
      | Anormal(n, _) | Amarker n -> Xset.mem predefined_annotations (P.name_to_string n)
      | _ -> false

  let has_user_defined_annotation ms =
    List.exists
      (fun m ->
        match m.m_desc with
        | Mannotation a -> not (is_predefined_annotation a)
        | _ -> false
      ) ms.ms_modifiers

  let has_static ms =
    List.exists
      (fun m ->
        match m.m_desc with
        | Mstatic -> true
        | _ -> false
      ) ms.ms_modifiers

  let check_JLS_level lv thunk error =
    (*let jls_to_string = function
      | Common.JLSnone -> "JLS?"
      | Common.JLS x -> sprintf "JLS%d" x
    in
    [%debug_log "env#java_lang_spec=%s" (jls_to_string env#java_lang_spec)];*)
    match env#java_lang_spec with
    | Common.JLS x when lv <= x -> begin
        env#set_actual_java_lang_spec lv;
        thunk()
    end
    | Common.JLS x when lv > x -> error()
    | _ -> error()


end (* of functor Parser_aux.F *)
]
