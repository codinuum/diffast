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
(* py_unparsing.ml *)

module Sourcecode = Diffast_core.Sourcecode
module Unparsing_base = Langs_common.Unparsing_base

module L = Py_label
module Tree = Sourcecode.Tree (L)

module Fmtr = struct
  let formatter = Format.std_formatter
end

module UPB = Unparsing_base.Make(Fmtr)

open UPB

let indent_unit = ref 4

let error_symbol = "###"

let pb = new ppbox

let pr_comma() = pr_string ","
let pr_eq()    = pr_string "="

let pr_a ?(head=pr_none) ?(tail=pr_none) sep pr a =
  if (Array.length a) > 0 then begin
    head();
    Array.iteri (fun i x -> if i > 0 then sep(); pr x) a;
    tail()
  end

let pr_opt pr = function None -> () | Some x -> pr x

let pr_indent level = pr_string (String.make (level * !indent_unit) ' ')

let pr_name = pr_string


let getlab nd =
  match nd#data#orig_lab_opt with
  | Some o -> (Obj.obj o : L.t)
  | None -> (Obj.obj nd#data#_label : L.t)

let get_nth_children = Sourcecode._get_logical_nth_child

let rec pr_node ?(fail_on_error=true) ?(level=0) node =
  let pr_node_ = pr_node ~fail_on_error in
  let children = node#initial_children in
  let nchildren = Array.length children in
  let pr_nth_child =
    if fail_on_error then
      fun ?(level=0) nth ->
        pr_node ~fail_on_error:true ~level children.(nth)
    else
      fun ?(level=0) nth ->
        try
          pr_node ~fail_on_error:false ~level children.(nth)
        with
          _ -> pr_string error_symbol
  in
  let pr_nth_children ?(head=pr_none) ?(sep=pad1) ?(tail=pr_none) ?(alt=pr_none) =
    if fail_on_error then begin
      fun ?(level=level) nth ->
        let ca = get_nth_children node nth in
        let is_empty = ca = [||] in
        if is_empty then
          alt()
        else
          head();
        pr_a sep (pr_node ~fail_on_error:true ~level) ca;
        if not is_empty then tail()
    end
    else
      fun ?(level=level) nth ->
        try
          let ca = get_nth_children node nth in
          let is_empty = ca = [||] in
          if is_empty then
            alt()
          else
            head();
          pr_a sep (pr_node ~fail_on_error:false ~level) ca;
          if not is_empty then tail()
        with
          _ -> pr_string error_symbol
  in
  let pr_uop uop = pr_string (L.UnaryOperator.to_simple_string uop) in
  let pr_bop bop = pr_string (L.BinaryOperator.to_simple_string bop) in
  let pr_aop aop = pr_string (L.AssignmentOperator.to_simple_string aop) in

  let pr_children ?(head=pr_none) ?(sep=pr_none) ?(level=level) () =
    pr_a ~head sep (pr_node_ ~level) children
  in
  let pr_space_children ?(head=pr_none) () = pr_a ~head pad1 pr_node_ children in
  let pr_comma_children ?(head=pr_none) () = pr_a ~head pr_comma pr_node_ children in

  let pr_newline_indent lv () = pr_newline(); pr_indent lv in
  let pr_newline_indent_ = pr_newline_indent level in

  let pr_suite = pr_nth_children ~sep:pr_none in

  let pr_expr_suite2 kw nth0 nth1 =
    pr_string kw; pad1(); pr_nth_child nth0; pr_colon();
    pr_suite nth1
  in
  let pr_expr_suite1 kw nth =
    pr_string kw; pr_colon();
    pr_suite nth
  in
  let pr_spc() =
    if nchildren > 0 then begin
      match getlab children.(0) with
      | L.Primary p -> begin
          match p with
          | L.Primary.Paren
          | L.Primary.Tuple
          | L.Primary.Test -> ()
          | _ -> pad1()
      end
      | _ -> pad1()
    end
  in

  match getlab node with
  | L.Dummy -> ()
  | L.ERROR -> pr_string "ERROR"

  | L.FileInput _ -> pr_children ~sep:pr_newline_indent_ ()

  | L.Statement stmt -> begin
      match stmt with
      | L.Statement.Simple -> pr_a pr_semicolon pr_node_ children; pr_newline()
      | L.Statement.If _ -> begin
          pr_expr_suite2 "if" 0 1;
          pr_nth_children ~head:pr_newline_indent_ ~sep:pr_newline_indent_ 2;
          pr_nth_children ~head:pr_newline_indent_ 3
      end
      | L.Statement.While  -> begin
          pr_expr_suite2 "while" 0 1;
          pr_nth_children ~head:pr_newline_indent_ 2
      end
      | L.Statement.For -> begin
          pr_string "for ";
          pr_nth_children ~sep:pr_comma 0; pr_string " in "; pr_nth_children ~sep:pr_comma 1;
          pr_colon();
          pr_suite 2;
          pr_nth_children ~head:pr_newline_indent_ 3
      end
      | L.Statement.Try -> begin
          pr_string "try:";
          pr_suite 0;
          pr_nth_children ~head:pr_newline_indent_ ~sep:pr_newline_indent_ 1;
          pr_nth_children ~head:pr_newline_indent_ 2;
          pr_nth_children ~head:pr_newline_indent_ 3
      end
      | L.Statement.With-> begin
          pr_string "with "; pr_nth_children ~sep:pr_comma 0; pr_colon(); pr_suite 1
      end
      | L.Statement.FuncDef _ -> begin
          pr_nth_children ~sep:pr_newline_indent_ ~tail:pr_newline_indent_ 0;
          pr_string "def "; pr_nth_children 1;
          pr_string "("; pr_nth_children 2; pr_string ")"; pr_nth_children 3; pr_colon();
          pr_suite 4
      end
      | L.Statement.AsyncFuncDef _ -> begin
          pr_nth_children ~sep:pr_newline_indent_ ~tail:pr_newline_indent_ 0;
          pr_string "async def "; pr_nth_children 1;
          pr_string "("; pr_nth_children 2; pr_string ")"; pr_nth_children 3; pr_colon();
          pr_suite 4
      end
      | L.Statement.ClassDef _ -> begin
          pr_nth_children ~sep:pr_newline_indent_ ~tail:pr_newline_indent_ 0;
          pr_string "class "; pr_nth_children 1; pr_nth_children 2; pr_colon();
          pr_suite 3
      end
      | L.Statement.Async -> pr_string "async "; pr_nth_child 0

      | L.Statement.ERROR -> pr_string "ERROR"

      | L.Statement.MARKER m -> pr_string m
  end
  | L.SimpleStatement sstmt -> begin
      match sstmt with
      | L.SimpleStatement.Expr -> pr_comma_children()
      | L.SimpleStatement.Assign aop -> begin
          pr_nth_children ~sep:pr_comma 0;
          pr_nth_children ~head:pr_colon 1;
          pr_nth_children ~head:(fun () -> pr_aop aop) ~sep:pr_comma 2
      end
      | L.SimpleStatement.Print    -> pr_string "print"; pr_spc() ; pr_comma_children()
      | L.SimpleStatement.Del      -> pr_string "del "; pr_comma_children()
      | L.SimpleStatement.Pass     -> pr_string "pass"
      | L.SimpleStatement.Break    -> pr_string "break"
      | L.SimpleStatement.Continue -> pr_string "continue"
      | L.SimpleStatement.Return   -> pr_string "return"; pr_comma_children ~head:pad1 ()
      | L.SimpleStatement.Raise when nchildren = 0 -> pr_string "raise";
      | L.SimpleStatement.Raise  -> pr_string "raise "; pr_comma_children()
      | L.SimpleStatement.Yield  -> pr_string "yield "; pr_comma_children()
      | L.SimpleStatement.Import -> pr_string "import "; pr_comma_children()
      | L.SimpleStatement.FromImport -> begin
          pr_string "from ";
          pr_nth_children ~tail:pad1 0;
          pr_string "import ";
          pr_nth_children ~sep:pr_comma ~alt:(fun () -> pr_string "*") 1
      end
      | L.SimpleStatement.Global -> pr_string "global "; pr_comma_children()
      | L.SimpleStatement.Exec -> begin
          pr_string "exec "; pr_nth_children 0;
          pr_nth_children ~head:(fun () -> pr_string " in ") 1;
          pr_nth_children ~head:pr_comma 2
      end
      | L.SimpleStatement.Assert -> pr_string "assert "; pr_comma_children()
      | L.SimpleStatement.RaiseFrom ->
          pr_string "raise "; pr_nth_child 0; pr_string " from "; pr_nth_child 1
      | L.SimpleStatement.Nonlocal -> pr_string "nonlocal "; pr_comma_children()
      | L.SimpleStatement.ERROR -> pr_string "ERROR"
  end

  | L.Primary prim -> begin
      match prim with
      | L.Primary.Name n      -> pr_name n
      | L.Primary.Literal lit -> begin
          match lit with
          | L.Literal.CatString (*s*)_ -> begin
              (*let re = Str.regexp_string "\n" in
              let s0 = Str.global_replace re "\\n" s in
              pr_string s0;*)
              pr_space_children()
          end
          | _ -> pr_string (L.Literal.to_simple_string lit)
      end
      | L.Primary.Paren        -> pr_string "("; pr_nth_child 0; pr_string ")"
      | L.Primary.Tuple        -> pr_string "("; pr_comma_children(); pr_string ")"
      | L.Primary.Yield        -> pr_string "yield "; pr_comma_children()
      | L.Primary.Test         ->
          pr_string "("; pr_nth_child 0; pad1(); pr_nth_child 1; pr_string ")"
      | L.Primary.List         -> pr_string "["; pr_comma_children(); pr_string "]"
      | L.Primary.ListFor -> begin
          pr_string "[";
          pr_nth_child 0;
          pad1();
          pr_nth_child 1;
          pr_nth_children ~head:pad1 2;
          pr_string "]"
      end
      | L.Primary.Dict -> begin
          pr_string "{";
          pr_nth_children ~sep:pr_comma 0;
          pr_nth_children ~head:pad1 1;
          pr_string "}"
      end
      | L.Primary.StringConv   -> pr_string "`"; pr_comma_children(); pr_string "`"
      | L.Primary.AttrRef _    -> pr_nth_child 0; pr_dot(); pr_nth_child 1
      | L.Primary.Subscription -> pr_nth_child 0; pr_string "["; pr_nth_children 1; pr_string "]"
      | L.Primary.Slicing      -> pr_nth_child 0; pr_string "["; pr_nth_children 1; pr_string "]"
      | L.Primary.Call _       -> pr_nth_child 0; pr_string "("; pr_nth_children 1; pr_string ")"
      | L.Primary.Await        -> pr_string "await "; pr_nth_child 0
      | L.Primary.Ellipsis     -> pr_string "..."
  end
  | L.UnaryOperator uo      -> pr_uop uo; pr_nth_child 0
  | L.BinaryOperator bo     -> pr_nth_child 0; pr_bop bo; pr_nth_child 1
  | L.Lambda                -> pr_string "lambda "; pr_nth_children 0; pr_colon(); pr_nth_children 1
  | L.Test                  ->
      pr_nth_child 0; pr_string " if "; pr_nth_child 1; pr_string " else "; pr_nth_child 2
  | L.Power                 -> pr_nth_child 0; pr_string "**"; pr_nth_child 1
  | L.From                  -> pr_string "from "; pr_nth_child 0
  | L.Named                 -> pr_nth_child 0; pr_string ":="; pr_nth_child 1

  (*| L.DottedName            -> pr_a pr_dot pr_node_ children*)
  | L.DottedName s          -> pr_string s
  | L.Name n                -> pr_name n

  | L.Elif _                -> pr_expr_suite2 "elif" 0 1
  | L.Else                  -> pr_expr_suite1 "else" 0
  | L.Finally               -> pr_expr_suite1 "finally" 0

  | L.Except -> begin
      pr_string "except";
      pr_nth_children ~head:pad1 0;
      pr_nth_children ~head:(fun () -> pr_string " as ") 1;
      pr_colon();
      pr_suite 2
  end

  | L.Suite
  | L.NamedSuite _ -> begin
      let lv = level + 1 in
      pr_newline_indent lv ();
      pr_children ~sep:(pr_newline_indent lv) ~level:lv ()
  end

  | L.Targets               -> pr_comma_children()
  | L.Target                -> pr_comma_children()
  | L.Parameters            -> pr_comma_children()
  | L.NamedParameters _     -> pr_comma_children()
  | L.Decorators _          -> pr_children ~sep:pr_newline_indent_ ()
  | L.Decorator n           ->
      pr_string "@"; pr_string n; pr_nth_children ~head:pr_lparen ~tail:pr_rparen 0
  | L.In                    -> pr_comma_children()
  | L.LHS                   -> pr_comma_children()
  | L.RHS                   -> pr_comma_children()
  | L.As                    -> pr_nth_child 0; pr_string " as "; pr_nth_child 1
  | L.ListIf                -> pr_string "if "; pr_nth_child 0; pr_nth_children 1
  | L.KeyDatum              -> pr_nth_child 0; pr_colon(); pr_nth_child 1
  | L.SliceItem             -> pr_nth_children 0; pr_colon(); pr_nth_children 1; pr_nth_children 2
  | L.Stride                -> pr_colon(); pr_nth_children 0
  | L.Annotation            -> pr_colon(); pr_nth_children 0
  | L.Ellipsis              -> pr_string "..."
  | L.Arguments _           -> pr_comma_children()
  | L.NamedArguments _      -> pr_comma_children()
  | L.Argument              -> pr_nth_child 0; pr_nth_children ~head:pr_eq 1
  | L.CompArgument          -> pr_nth_child 0; pad1(); pr_nth_child 1
  | L.AssignArgument        -> pr_nth_child 0; pr_string ":="; pr_nth_child 1
  | L.Slash                 -> pr_string "/"
  | L.Star                  -> pr_string "*"; pr_nth_children 0
  | L.StarStar              -> pr_string "**"; pr_nth_child 0
  | L.GenFor -> begin
      pr_string "for "; pr_nth_child 0;
      pr_string " in "; pr_nth_child 1;
      pr_nth_children ~head:pad1 2
  end
  | L.AsyncGenFor -> begin
      pr_string "async for "; pr_nth_child 0;
      pr_string " in "; pr_nth_child 1;
      pr_nth_children ~head:pad1 2
  end
  | L.GenIf                 -> pr_string "if "; pr_nth_child 0; pr_nth_children ~head:pad1 1
  | L.Inheritance           -> pr_string "("; pr_comma_children(); pr_string ")"
  | L.Chevron               -> pr_string ">>"; pr_nth_child 0
  | L.Yield                 -> pr_string "yield "; pr_comma_children()
  | L.ParamDef _            -> pr_nth_child 0; pr_eq(); pr_nth_children 1
  | L.ListParamDef          -> pr_comma_children()
  | L.TypedParamDef _       -> pr_nth_child 0; pr_colon(); pr_nth_child 1
  | L.WithItem              -> pr_nth_child 0; pr_nth_children ~head:(fun () -> pr_string " as ") 1
  | L.ReturnAnnotation      -> pr_string "->"; pr_nth_child 0
  | L.Dots i                -> pr_string (String.make i '.')

  | L.Comment c             -> pr_string c


let unparse ?(no_boxing=false) ?(no_header=false) ?(fail_on_error=true) t =
  let prev_boxing_flag = pb#boxing_flag in
  if no_boxing && prev_boxing_flag then begin
    Format.open_hbox();
    pb#disable_boxing()
  end;

  pb#open_vbox 0;
  if not no_header then begin
    pr_string "# generated by Diff/AST Python Unparser"; pr_cut();
  end;
  if not fail_on_error && not no_header then begin
    pr_string (Printf.sprintf "# error_symbol=\"%s\"" error_symbol); pr_cut();
  end;
  pr_node ~fail_on_error t;
  pr_newline();
  pb#close_box();
  pr_flush();

  if no_boxing && prev_boxing_flag then begin
    pb#enable_boxing();
    Format.close_box()
  end
