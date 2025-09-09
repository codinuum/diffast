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
 * An unparser for the Java Language
 *
 * java_unparsing.ml
 *
 *)

module Xlist = Diffast_misc.Xlist
module L = Java_label

module Fmtr = struct
  let formatter = Format.std_formatter
end

module UPB = Langs_common.Unparsing_base.Make(Fmtr)

open UPB

let pb = new ppbox

let error_symbol = "#"

let getlab nd =
  match nd#data#orig_lab_opt with
  | Some o -> (Obj.obj o : L.t)
  | None -> (Obj.obj nd#data#_label : L.t)

let has_different_orig_lab nd =
  match nd#data#orig_lab_opt with
  | Some o -> (Obj.obj o : L.t) <> (Obj.obj nd#data#_label : L.t)
  | None -> false


(* precedence of operators
 *
 * 17: []  .  (params)                       left
 * 16: expr++  expr--                        left
 * 15: ++expr  --expr  +expr  -expr  ~  !    right
 * 14: new  (type)expr                       right
 * 13: *  /  %                               left
 * 12: +  -                                  left
 * 11: <<  >>  >>>                           left
 * 10: <  >  >=  <=  instanceof              noassoc
 *  9: ==  !=                                left
 *  8: &                                     left
 *  7: ^                                     left
 *  6: |                                     left
 *  5: &&                                    left
 *  4: ||                                    left
 *  3: ?:                                    right
 *  2: =  +=  -=  *=  /=  %=                 right
       >>=  <<=  >>>=  &=  ^=  |=
 *  1: ->                                    right
 *
 *)

let get_prec_of_sym = function
  | "." | "[]" -> 17
  | "::" -> 17 (* ??? *)
  | _ -> 0


let prec_of_assignment_operators = 2



let get_prec_of_primary = function
  | L.Primary.Name _ | L.Primary.AmbiguousName _ -> 17
  | L.Primary.InstanceCreation _
  | L.Primary.ArrayCreationDims _
  | L.Primary.ArrayCreationInit -> 14
  | _ -> 0

let get_prec_of_expression = function
  | L.Expression.UnaryOperator uop -> begin
      match uop with
      | L.UnaryOperator.PostIncrement
      | L.UnaryOperator.PostDecrement -> 16
      | L.UnaryOperator.PreIncrement
      | L.UnaryOperator.PreDecrement
      | L.UnaryOperator.Positive
      | L.UnaryOperator.Negative
      | L.UnaryOperator.Complement
      | L.UnaryOperator.Not -> 15
  end
  | L.Expression.BinaryOperator bop -> begin
      match bop with
      | L.BinaryOperator.Mul
      | L.BinaryOperator.Div
      | L.BinaryOperator.Mod -> 13
      | L.BinaryOperator.Add
      | L.BinaryOperator.Sub -> 12
      | L.BinaryOperator.ShiftL
      | L.BinaryOperator.ShiftR
      | L.BinaryOperator.ShiftRU -> 11
      | L.BinaryOperator.Lt
      | L.BinaryOperator.Gt
      | L.BinaryOperator.Le
      | L.BinaryOperator.Ge -> 10
      | L.BinaryOperator.Eq
      | L.BinaryOperator.Neq -> 9
      | L.BinaryOperator.BitAnd -> 8
      | L.BinaryOperator.BitXor -> 7
      | L.BinaryOperator.BitOr -> 6
      | L.BinaryOperator.And -> 5
      | L.BinaryOperator.Or -> 4
  end
  | L.Expression.AssignmentOperator _ -> 2
  | L.Expression.Primary p -> get_prec_of_primary p
  | L.Expression.Cast -> 14
  | L.Expression.Instanceof -> 10
  | L.Expression.Cond -> 3
  | L.Expression.Lambda -> 0
  | L.Expression.Switch -> 0
  | L.Expression.NaryAdd -> 12

let get_prec = function
  | L.Primary p    -> get_prec_of_primary p
  | L.Expression e -> get_prec_of_expression e
  | _ -> 0

let find_nodes filt a =
  Array.of_list
    (List.filter (fun nd -> filt (getlab nd)) (Array.to_list a))

let escaped_dollar_pat = Str.regexp_string "&#36;"
let unescape_dollar = Str.global_replace escaped_dollar_pat "$"

let dollar_pat = Str.regexp_string "$"
let norm_fqn x = unescape_dollar (Str.global_replace dollar_pat "." x)

let sep_pat = Str.regexp "[.$]"
let get_last_id name =
  if name = "" then
    ""
  else
    Xlist.last (Str.split sep_pat name)

let undeco_pat = Str.regexp "#[0-9]+"
let undeco x = Str.global_replace undeco_pat "" (unescape_dollar x)

let pr_id x = pr_id (unescape_dollar x)
let pr_name x = pr_name (unescape_dollar x)

let rec pr_node ?(fail_on_error=true) ?(va=false) ?(blk_style=BSshort) ?(prec=0) node =

(*pr_string (L.to_string (getlab node));*)

(*let pr_node_ = pr_node ~blk_style ~prec in*)

  let children = node#initial_children in
  let nchildren = Array.length children in

  (*let pr_nth_child nth = apply_nth pr_node children nth in*)
  let pr_nth_child =
    if fail_on_error then
      fun ?(va=false) ?(blk_style=BSshort) ?(prec=0) nth ->
        pr_node ~fail_on_error:true ~va ~blk_style ~prec children.(nth)
    else
      fun ?(va=false) ?(blk_style=BSshort) ?(prec=0) nth ->
        try
          pr_node ~fail_on_error:false ~va ~blk_style ~prec children.(nth)
        with
          _ -> pr_string error_symbol
  in
  let spc ?(blk_style=BSshort) n =
    match blk_style with
    | BSshort -> pad n
    | BStall -> pr_break n 0
  in

  match getlab node with
  | L.Error s -> pr_string s

  | L.CatchParameter(n, dims) ->
      pb#open_box pb#indent;
      pr_selected ~fail_on_error L.is_modifiers children;
      pr_selected ~fail_on_error ~sep:pr_bor ~tail:pr_space L.is_type children;
      pr_id n; pr_dims dims;
      pb#close_box()

  | L.ResourceSpec ->
      pr_lparen();
      pb#pr_hova pr_semicolon (pr_node ~fail_on_error) children;
      pr_rparen()

  (*| L.Resource(n, dims) ->
      pb#open_box pb#indent;
      pr_selected ~fail_on_error L.is_modifiers children;
      pr_selected ~fail_on_error ~tail:pr_space L.is_type children;
      pr_id n; pr_dims dims; pad 1; pr_string "="; pr_space();
      pr_selected ~fail_on_error L.is_expression children;
      pb#close_box()*)

  | L.InferredFormalParameter n -> pr_string n
  | L.InferredFormalParameters ->
      pr_lparen(); pb#pr_a pr_comma (pr_node ~fail_on_error) children; pr_rparen()

  | L.CompilationUnit
  | L.ImportDeclarations
  | L.TypeDeclarations
    ->
      pb#pr_a force_newline (pr_node ~fail_on_error) children

  | L.PackageDeclaration n ->
      pr_selected ~fail_on_error ~sep:pr_space ~tail:pr_space L.is_annotation children;
      pr_string "package "; pr_name n; pr_semicolon()

  | L.IDsingle n           -> pr_string "import "; pr_name n; pr_semicolon()
  | L.IDtypeOnDemand n     -> pr_string "import "; pr_name n; pr_string ".*;"
  | L.IDsingleStatic(n, i) ->
      pr_string "import static "; pr_name n; pr_dot(); pr_id i; pr_semicolon()

  | L.IDstaticOnDemand n   -> pr_string "import static "; pr_name n; pr_string ".*;"

  | L.Annotations -> pb#pr_a ~tail:pr_space pr_space (pr_node ~fail_on_error) children

  | L.Annotation a -> begin
      match a with
      | L.Annotation.Normal n ->
          pr_string "@"; pr_name n; pr_lparen();
          pb#pr_va pr_comma (pr_node ~fail_on_error) children;
          pr_rparen()

      | L.Annotation.Marker n -> pr_string "@"; pr_name n

      | L.Annotation.SingleElement n ->
          pr_string "@"; pr_name n; pr_lparen();
          pr_nth_child 0;
          pr_rparen()
  end

  | L.Modifiers _ -> pb#pr_a ~tail:pr_space pr_space (pr_node ~fail_on_error) children

  | L.Modifier m -> begin
      begin
        match m with
        | L.Modifier.Public       -> pr_string "public"
        | L.Modifier.Protected    -> pr_string "protected"
        | L.Modifier.Private      -> pr_string "private"
        | L.Modifier.Static       -> pr_string "static"
        | L.Modifier.Abstract     -> pr_string "abstract"
        | L.Modifier.Final        -> pr_string "final"
        | L.Modifier.Native       -> pr_string "native"
        | L.Modifier.Synchronized -> pr_string "synchronized"
        | L.Modifier.Transient    -> pr_string "transient"
        | L.Modifier.Volatile     -> pr_string "volatile"
        | L.Modifier.Strictfp     -> pr_string "strictfp"
(*      | L.Modifier.Annotation   -> pr_nth_child 0*)
        | L.Modifier.Default      -> pr_string "default"
        | L.Modifier.Transitive   -> pr_string "transitive"
        | L.Modifier.Sealed       -> pr_string "sealed"
        | L.Modifier.NonSealed    -> pr_string "non-sealed"
        | L.Modifier.Error s      -> pr_string s
      end
  end

  | L.ElementValuePair i -> pr_id i; pr_string "="; pr_nth_child 0
  | L.EVconditional      -> pr_nth_child 0
  | L.EVannotation       -> pr_nth_child 0
  | L.EVarrayInit ->
      pb#open_box 0;
      pr_string "{"; pb#pr_a pr_comma (pr_node ~fail_on_error) children; pr_string "}";
      pb#close_box()

  | L.Specifier _ -> ()

  | L.Module n ->
      pb#open_vbox 0;
      pb#open_box 0;
      pr_selected ~fail_on_error ~blk_style ~tail:pr_space L.is_annotation children;
      pr_selected ~fail_on_error ~tail:pad1 L.is_open children;
      pr_string "module "; pr_name n;
      pb#close_box();
      pr_selected ~fail_on_error ~blk_style L.is_module_body children;
      pb#close_box()

  | L.Open -> pr_string "open"
  | L.ModuleName n -> pr_name n

  | L.Requires n ->
      pb#open_box 0;
      pr_string "requires ";
      pr_selected ~fail_on_error ~head:pr_space ~tail:pr_space L.is_modifier children;
      pr_name n;
      pr_semicolon();
      pb#close_box()

  | L.Exports n ->
      pb#open_box 0;
      pr_string "exports "; pr_name n;
      let pr_to () = pr_space(); pr_string "to"; pr_space() in
      pb#pr_a ~head:pr_to pr_comma (pr_node ~fail_on_error) children;
      pr_semicolon();
      pb#close_box()

  | L.Opens n ->
      pb#open_box 0;
      pr_string "opens "; pr_name n;
      let pr_to () = pr_space(); pr_string "to"; pr_space() in
      pb#pr_a ~head:pr_to pr_comma (pr_node ~fail_on_error) children;
      pr_semicolon();
      pb#close_box()

  | L.Uses n -> pr_string "uses "; pr_name n; pr_semicolon()

  | L.Provides n ->
      pb#open_box 0;
      pr_string "provides "; pr_name n;
      let pr_with () = pr_space(); pr_string "with"; pr_space() in
      pb#pr_a ~head:pr_with pr_comma (pr_node ~fail_on_error) children;
      pr_semicolon();
      pb#close_box()

  | L.Class i ->
      let specs = get_specs children in
      pb#open_vbox 0;
      pb#open_box 0;
      pr_selected ~fail_on_error ~head:(fun () -> pb#open_vbox 0) ~tail:pb#close_box L.is_modifiers specs;
      pr_string "class "; pr_id i;
      pr_selected ~fail_on_error L.is_typeparameters specs;
      pr_selected ~fail_on_error L.is_extends specs;
      pr_selected ~fail_on_error L.is_implements specs;
      pr_selected ~fail_on_error L.is_permits specs;
      pb#close_box();
      pr_selected ~fail_on_error ~blk_style L.is_classbody children;
      pb#close_box()

  | L.Enum i ->
      let specs = get_specs children in
      pb#open_vbox 0;
      pb#open_box 0;
      pr_selected ~fail_on_error ~head:(fun () -> pb#open_vbox 0) ~tail:pb#close_box L.is_modifiers specs;
      pr_string "enum "; pr_id i;
      pr_selected ~fail_on_error L.is_implements specs;
      pb#close_box();
      pr_selected ~fail_on_error ~blk_style L.is_enumbody children;
      pb#close_box()

  | L.Record i ->
      let specs = get_specs children in
      pb#open_vbox 0;
      pb#open_box 0;
      pr_selected ~fail_on_error ~head:(fun () -> pb#open_vbox 0) ~tail:pb#close_box L.is_modifiers specs;
      pr_string "record "; pr_id i;
      pr_selected ~fail_on_error L.is_typeparameters specs;
      pr_lparen(); pr_selected ~fail_on_error ~sep:pr_comma L.is_parameter specs; pr_rparen();
      pr_selected ~fail_on_error L.is_implements specs;
      pb#close_box();
      pr_selected ~fail_on_error ~blk_style L.is_classbody children;
      pb#close_box()

  | L.Interface i ->
      let specs = get_specs children in
      pb#open_vbox 0;
      pb#open_box 0;
      pr_selected ~fail_on_error ~head:(fun () -> pb#open_vbox 0) ~tail:pb#close_box L.is_modifiers specs;
      pr_string "interface "; pr_id i;
      pr_typeparameters ~fail_on_error specs;
      pr_selected ~fail_on_error L.is_extendsinterfaces specs;
      pr_selected ~fail_on_error L.is_permits specs;
      pb#close_box();
      pr_selected ~fail_on_error ~blk_style L.is_interfacebody children;
      pb#close_box()

  | L.AnnotationType i ->
      let specs = get_specs children in
      pb#open_vbox 0;
      pb#open_box 0;
      pr_selected ~fail_on_error ~head:(fun () -> pb#open_vbox 0) ~tail:pb#close_box L.is_modifiers specs;
      pr_string "@interface "; pr_id i;
      pb#close_box();
      pr_selected ~fail_on_error ~blk_style L.is_annotationtypebody children;
      pb#close_box()

  | L.Aspect i ->
      let specs = get_specs children in
      pb#open_vbox 0;
      pb#open_box 0;
      pr_selected ~fail_on_error ~head:(fun () -> pb#open_vbox 0) ~tail:pb#close_box L.is_modifiers specs;
      pr_string "aspect"; pr_space(); pr_id i;
      pr_selected ~fail_on_error L.is_extends specs;
      pr_selected ~fail_on_error L.is_implements specs;
      pb#close_box();
      pr_selected ~fail_on_error ~blk_style L.is_classbody children;
      pb#close_box()

  | L.Pointcut i ->
      pb#open_vbox 0;
      pb#open_box 0;
      pr_selected ~fail_on_error ~head:(fun () -> pb#open_vbox 0) ~tail:pb#close_box L.is_modifiers children;
      pr_string "pointcut"; pr_space(); pr_id i;
      pr_parameters ~fail_on_error children;
      pr_selected ~fail_on_error ~head:pr_colon L.is_pointcut_expr children;
      pb#close_box();
      pr_semicolon();
      pb#close_box()

  | L.DeclareParents ->
      pr_string "declare"; pr_space(); pr_string "parents";
      pr_selected ~fail_on_error ~head:pr_colon L.is_classname_pattern_expr children;
      pr_selected ~fail_on_error L.is_extends children;
      pr_selected ~fail_on_error L.is_implements children;
      pr_semicolon()

  | L.DeclareMessage k ->
      pr_string "declare"; pr_space(); pr_string k;
      pr_selected ~fail_on_error ~head:pr_colon L.is_pointcut_expr children;
      pr_selected ~fail_on_error ~head:pr_colon L.is_primary children;
      pr_semicolon()

  | L.DeclareSoft ->
      pr_string "declare"; pr_space(); pr_string "soft";
      pr_selected ~fail_on_error ~head:pr_colon L.is_pointcut_expr children;
      pr_semicolon()

  | L.DeclarePrecedence ->
      pr_string "declare"; pr_space(); pr_string "precedence";
      pr_selected ~fail_on_error ~head:pr_colon ~sep:pr_comma L.is_classname_pattern_expr children;
      pr_semicolon()

  | L.PointcutAnd -> pr_nth_child 0; pr_space(); pr_string "&&"; pr_space(); pr_nth_child 1
  | L.PointcutOr -> pr_nth_child 0; pr_space(); pr_string "||"; pr_space(); pr_nth_child 1
  | L.PointcutNot -> pr_string "!"; pr_nth_child 0
  | L.PointcutParen -> pr_lparen(); pr_nth_child 0; pr_rparen()
  | L.PointcutWithin -> pr_string "within"; pr_lparen(); pr_nth_child 0; pr_rparen()

  | L.ClassnamePatternAnd -> pr_nth_child 0; pr_space(); pr_string "&&"; pr_space(); pr_nth_child 1
  | L.ClassnamePatternOr -> pr_nth_child 0; pr_space(); pr_string "||"; pr_space(); pr_nth_child 1
  | L.ClassnamePatternNot -> pr_string "!"; pr_nth_child 0
  | L.ClassnamePatternParen -> pr_lparen(); pr_nth_child 0; pr_rparen()
  | L.ClassnamePatternName n -> pr_name n
  | L.ClassnamePatternNamePlus n -> pr_name n; pr_string "+"

  | L.ModuleBody _ ->
        if nchildren = 0 then
          pr_string "{}"
        else begin
          pb#pr_block_begin_tall();
          pb#pr_a pr_cut (pr_node ~fail_on_error) children;
          pb#pr_block_end()
        end

  | L.ClassBody _ ->
        if nchildren = 0 then
          pr_string "{}"
        else begin
          pb#pr_block_begin_tall();
          pb#pr_a pr_cut (pr_node ~fail_on_error) children;
          pb#pr_block_end()
        end

  | L.EnumBody _ ->
        if nchildren = 0 then
          pr_string "{}"
        else begin
          pb#pr_block_begin_tall();
          pr_selected ~fail_on_error ~pra:pb#pr_hova ~sep:pr_comma L.is_enumconstant children;
          begin
            try
              Array.iter
                (fun c ->
                  let clab = getlab c in
                  if L.is_classbodydecl clab then begin
                    if not (L.is_emptydecl clab) then begin
                      pr_semicolon(); pr_space()
                    end;
                    raise Exit
                  end
                ) children
            with
              Exit -> ()
          end;
          pr_selected ~fail_on_error ~blk_style ~sep:pr_space L.is_classbodydecl children;
          pb#pr_block_end()
        end

  | L.InterfaceBody _ ->
        if nchildren = 0 then
          pr_string "{}"
        else begin
          pb#pr_block_begin_tall();
          pb#pr_a pr_space (pr_node ~fail_on_error) children;
          pb#pr_block_end()
        end

  | L.AnnotationTypeBody _ ->
        if nchildren = 0 then
          pr_string "{}"
        else begin
          pb#pr_block_begin_tall();
          pb#pr_a pr_space (pr_node ~fail_on_error) children;
          pb#pr_block_end()
        end

  | L.EnumConstant i ->
      pr_selected ~fail_on_error ~blk_style ~tail:pr_space L.is_annotations children;
      pr_id i;
      pr_selected ~fail_on_error ~head:pr_lparen ~tail:pr_rparen L.is_arguments children;
      pr_selected ~fail_on_error ~blk_style L.is_classbody children

  | L.Super -> ()

  | L.ThisInvocation ->
      pr_typearguments ~fail_on_error children;
      pr_string "this"; pr_arguments ~fail_on_error children; pr_semicolon()

  | L.SuperInvocation ->
      pr_typearguments ~fail_on_error children;
      pr_string "super"; pr_arguments ~fail_on_error children; pr_semicolon()

  | L.PrimaryInvocation ->
      pr_nth_child ~blk_style ~prec:(get_prec_of_sym ".") 0;
      pr_dot();
      pr_typearguments ~fail_on_error children;
      pr_string "super"; pr_arguments ~fail_on_error children; pr_semicolon()

  | L.NameInvocation n ->
      pr_name n; pr_dot();
      pr_typearguments ~fail_on_error children;
      pr_string "super"; pr_arguments ~fail_on_error children; pr_semicolon()

  | L.Constructor(name, _) ->
      (*pb#open_vbox 0;*)
      pb#open_box 0;
      pr_selected ~fail_on_error ~head:(fun () -> pb#open_vbox 0) ~tail:pb#close_box L.is_modifiers children;
      pr_typeparameters ~fail_on_error children;
      pr_id name;
      pr_parameters ~fail_on_error children; pad 1;
      pr_selected ~fail_on_error L.is_throws children;
      pb#close_box();
      pr_selected ~fail_on_error ~blk_style L.is_ctorbody children;
      (*pb#close_box()*)

  | L.ConstructorBody _ ->
      pb#pr_block_begin_short();
      pr_selected ~fail_on_error ~sep:pr_space
        (fun lab -> L.is_explicitctorinvok lab || L.is_blockstatement lab || L.is_error lab)
        children;
      pb#pr_block_end()

  | L.StaticInitializer ->
      pr_string "static "; pr_nth_child ~blk_style:BStall ~prec 0

  | L.InstanceInitializer -> pr_nth_child ~blk_style:BStall ~prec 0

  | L.Block _ ->
      if nchildren = 0 then
        pr_string "{}"
      else begin
        pb#pr_block_begin blk_style;
        pb#pr_a pr_space (pr_node ~fail_on_error) children;
        pb#pr_block_end()
      end

  | L.Wildcard ->
      pr_selected ~fail_on_error ~sep:pr_space ~tail:pr_space L.is_annotations children;
      pr_string "?";
      pr_selected ~fail_on_error L.is_wildcard_bounds children

  | L.WildcardBoundsExtends -> pr_string " extends "; pr_nth_child 0
  | L.WildcardBoundsSuper -> pr_string " super "; pr_nth_child 0

  | L.Extends ->
      pr_break 1 pb#indent;
      pr_string "extends ";
      pr_nth_child 0

  | L.Implements when nchildren = 0 -> ()
  | L.Implements ->
      pr_break 1 pb#indent;
      pr_string "implements ";
      pb#pr_hova pr_comma (pr_node ~fail_on_error) children

  | L.ExtendsInterfaces when nchildren = 0 -> ()
  | L.ExtendsInterfaces ->
      pr_break 1 pb#indent;
      pr_string "extends ";
      pb#pr_hova pr_comma (pr_node ~fail_on_error) children

  | L.Permits when nchildren = 0 -> ()
  | L.Permits ->
      pr_break 1 pb#indent;
      pr_string "permits ";
      pb#pr_hova pr_comma (pr_node ~fail_on_error) children

  | L.TypeName n -> pr_name n

  | L.ElementDeclaration i ->
      pb#open_box 0;
      pr_selected ~fail_on_error L.is_modifiers children;
      pr_selected ~fail_on_error L.is_type children; pad 1; pr_id i; pr_string "()";
      pr_selected ~fail_on_error L.is_annot_dim children;
      pr_selected ~fail_on_error ~head:(fun _ -> pr_string " default ")
        L.is_elementvalue children;
      pr_semicolon();
      pb#close_box()

  | L.AnnotDim ellipsis ->
      pr_selected ~fail_on_error ~sep:pr_space(* ~tail:pr_space*) L.is_annotations children;
      if ellipsis then
        ()
      else
        pr_string "[]";

  | L.FieldDeclarations _ -> pb#pr_a pr_space (pr_node ~fail_on_error) children

  | L.FieldDeclaration _ ->
      pb#open_box 0;
      pr_selected ~fail_on_error L.is_modifiers children;
      pr_selected ~fail_on_error ~tail:pr_space L.is_type children;
      pr_selected ~fail_on_error ~sep:pr_comma ~tail:pr_semicolon
        L.is_variabledeclarator children;
      pb#close_box()

  | L.VariableDeclaration -> ()

  | L.EmptyDeclaration -> pr_semicolon()

  | L.Primary p -> pr_primary ~fail_on_error ~prec p children

  | L.Expression e -> pr_expression ~fail_on_error ~prec e children

  | L.TypeArguments _ ->
      pr_string "<"; pb#pr_a _pr_comma (pr_node ~fail_on_error) children; pr_string ">";

  | L.NamedArguments _ | L.Arguments -> pb#pr_a pr_comma (pr_node ~fail_on_error) children

  | L.TypeParameters _ ->
      pr_string "<"; pb#pr_a _pr_comma (pr_node ~fail_on_error) children; pr_string ">"

  | L.TypeParameter i ->
      pr_selected ~fail_on_error ~sep:pr_space ~tail:pr_space L.is_annotation children;
      pr_id i;
      pr_selected ~fail_on_error ~head:(fun () -> pr_string " extends ") L.is_type_bound children;

  | L.TypeBound -> pb#pr_a pr_amp (pr_node ~fail_on_error) children

  | L.Type ty ->
      if nchildren = 0 then begin
        pr_string (type_to_string ~va ty)
      end
      else begin
        let rec pr_ty = function
          | (L.Type.Byte
          | L.Type.Short
          | L.Type.Int
          | L.Type.Long
          | L.Type.Char
          | L.Type.Float
          | L.Type.Double
          | L.Type.Boolean) as ty0 -> begin
              pr_selected ~fail_on_error ~sep:pr_space ~tail:pr_space L.is_annotation children;
              pr_string (type_to_string ty0)
          end
          | L.Type.ClassOrInterface n
          | L.Type.Class n
          | L.Type.Interface n -> begin
              pr_selected ~fail_on_error ~tail:pr_dot L.is_type children;
              pr_selected ~fail_on_error ~sep:pr_space ~tail:pr_space L.is_annotation children;
              pr_name n;
              pr_selected ~fail_on_error L.is_typearguments children
          end
          (*| L.Type.Array(ty, dims) when va && dims = 1 -> pr_ty ty
          | L.Type.Array(ty, dims) when va -> pr_ty ty; pr_dims (dims-1)*)
          | L.Type.Array(ty, dims) ->
              pr_ty ty;
              pr_selected ~fail_on_error ~otherwise:(fun () -> pr_dims dims) L.is_annot_dim children

          | L.Type.Void -> pr_string "void"
        in
        pr_ty ty
      end

  | L.Qualifier n -> pr_name n; pr_dot()

  | L.DimExpr -> pr_nth_child 0

  | L.ArrayInitializer ->
      pr_string "{"; pr_space();
      pb#pr_a pr_comma (pr_node ~fail_on_error) children; pr_space();
      pr_string "}"

  | L.HugeArray(_, c) -> pr_string c
  | L.HugeExpr(_, c) -> pr_string c

  | L.Throws _ when nchildren = 0 -> ()
  | L.Throws _ ->
      pr_break 1 pb#indent; pr_string "throws "; pr_types ~fail_on_error children

  | L.Parameters _ -> pb#pr_hova pr_comma (pr_node ~fail_on_error) children

  | L.Parameter(i, dims, va) ->
      pb#open_hbox();
      pr_selected ~fail_on_error L.is_modifiers children;
      pb#close_box();

      (*pr_selected ~fail_on_error L.is_type children;*)
      let a' = find_nodes L.is_type children in
      if (Array.length a') > 0 then begin
        pb#pr_a pr_none (pr_node ~fail_on_error ~va ~blk_style ~prec) a';
      end;

      if va then pr_string "...";
      pad 1;
      pr_id i;
      pr_selected ~fail_on_error ~otherwise:(fun () -> pr_dims dims) L.is_annot_dim children

  | L.ReceiverParameter id_opt ->
      pb#open_hbox();
      pr_selected ~fail_on_error L.is_modifiers children;
      pb#close_box();

      (*pr_selected ~fail_on_error L.is_type children;*)
      let a' = find_nodes L.is_type children in
      if (Array.length a') > 0 then begin
        pb#pr_a pr_none (pr_node ~fail_on_error ~va ~blk_style ~prec) a';
      end;

      pad 1;

      begin
        match id_opt with
        | Some id -> pr_id id; pr_dot()
        | _ -> ()
      end;
      pr_string "this"

  | L.ForHead _ ->
      pr_selected ~fail_on_error L.is_forinit children;
      pr_semicolon(); pr_space();
      pr_selected ~fail_on_error L.is_forcond children;
      pr_semicolon(); pr_space();
      pr_selected ~fail_on_error L.is_forupdate children;

  | L.Method(i, _) ->
      (*pb#open_vbox 0;*)
      pb#open_box 0;
      let opv () = pb#open_vbox 0 in
      pr_selected ~fail_on_error ~head:opv ~tail:pb#close_box L.is_modifiers children;
      pr_typeparameters ~fail_on_error children;
      pr_selected ~fail_on_error L.is_type children; pad 1;
      pr_id i;
      pr_parameters ~fail_on_error children;
      pr_selected ~fail_on_error L.is_annot_dim children;
      pr_selected ~fail_on_error L.is_throws children;
      pb#close_box();
      pr_selected ~fail_on_error ~blk_style ~head:pad1 ~otherwise:pr_semicolon
        L.is_methodbody children;
      (*pb#close_box()*)

  | L.MethodBody _ ->
      if nchildren = 0 then
        pr_string "{}"
      else begin
        pb#pr_block_begin_short();
        pb#pr_a pr_space (pr_node ~fail_on_error) children;
        pb#pr_block_end()
      end

  | L.ForInit _ -> pb#pr_a pr_comma (pr_node ~fail_on_error) children
  | L.ForCond _ -> pr_nth_child 0
  | L.ForUpdate _ -> pb#pr_a pr_comma (pr_node ~fail_on_error) children

  | L.Finally -> pr_string "finally"; pr_nth_child 0
  | L.CatchClause _ ->
      pr_string "catch ("; pr_nth_child 0; pr_rparen();
      begin
        try
          if L.is_block (getlab (children.(1))) then
            pad 1
          else
            pr_break 1 pb#indent;
        with
          _ -> pad 1
      end;
      pr_nth_child 1

  | L.SLconstant _ ->
      pr_string "case "; pb#pr_a pr_comma (pr_node ~fail_on_error) children; pr_string ":"
  | L.SLdefault -> pr_string "default:"

  | L.SRLconstant ->
      pr_string "case "; pb#pr_a pr_comma (pr_node ~fail_on_error) children; pr_string " ->"
  | L.SRLdefault -> pr_string "default ->"

  | L.SwitchBlock ->
      pb#pr_block_begin_short();
      pr_selected ~fail_on_error ~blk_style ~sep:pr_space L.is_switchblockstmtgroup children;
      pr_selected ~fail_on_error ~blk_style ~sep:pr_space L.is_switchrule children;
      pb#pr_block_end()

  | L.SwitchBlockStatementGroup ->
      pb#open_vbox 0;
      pr_selected ~fail_on_error ~sep:pr_space L.is_switchlabel children; pr_break 1 pb#indent;
      pb#open_vbox 0;
      pr_selected ~fail_on_error ~sep:pr_space
        (fun lab -> L.is_block lab || L.is_blockstatement lab)
        children;
      pb#close_box();
      pb#close_box()

  | L.SwitchRule ->
      pb#open_vbox 0;
      pr_selected ~fail_on_error ~sep:pr_space L.is_switchrulelabel children; pr_break 1 pb#indent;
      pb#open_vbox 0;
      pr_selected ~fail_on_error ~sep:pr_space ~tail:pr_semicolon L.is_expression children;
      pr_selected ~fail_on_error ~sep:pr_space
        (fun lab -> L.is_block lab || L.is_statement lab)
        children;
      pb#close_box();
      pb#close_box()

  | L.Statement stmt -> begin
      match stmt with
      | L.Statement.Empty -> pr_semicolon()

      | L.Statement.Assert ->
          pr_string "assert "; pr_nth_child 0;
          if nchildren > 1 then begin
            pr_string ":"; pr_nth_child 1
          end;
          pr_semicolon()

      | L.Statement.If _ ->
          pr_string "if ("; pr_nth_child 0; pr_rparen();
          begin
            try
              if L.is_block (getlab (children.(1))) then
                pad 1
              else
                pr_break 1 pb#indent;
            with
              _ -> pad 1
          end;
          if nchildren < 2 then
            pr_string "{}"
          else begin
            pr_nth_child 1;
            if nchildren > 2 then begin
              pr_selected ~fail_on_error ~head:pad1 ~sep:pad1 L.is_elseif children;
              pr_selected ~fail_on_error ~head:pad1 L.is_else children;

              let else_part = children.(nchildren - 1) in
              let lab = getlab else_part in
              if not (L.is_elseif lab || L.is_else lab) then begin
                spc ~blk_style 1; pr_string "else";
                let else_lab = getlab else_part in
                if L.is_block else_lab || L.is_if else_lab then
                  pad 1
                else
                  pr_break 1 pb#indent;
                pr_node ~fail_on_error else_part
              end

            end
          end

      (*| L.Statement.FlattenedIf _ ->
          if nchildren > 0 then begin
            pb#open_vbox pb#indent;
            pb#pr_a (fun () -> pr_string " ") (pr_node ~fail_on_error) children;
            pb#close_box()
          end*)

      | L.Statement.ElseIf _ ->
          pr_string "else if ("; pr_nth_child 0; pr_rparen();
          begin
            try
              if L.is_block (getlab (children.(1))) then
                pad 1
              else
                pr_break 1 pb#indent;
            with
              _ -> pad 1
          end;
          if nchildren < 2 then
            pr_string "{}"
          else
            pr_nth_child 1

      | L.Statement.Else ->
          pr_string "else";
          begin
            try
              if L.is_block (getlab (children.(0))) then
                pad 1
              else
                pr_break 1 pb#indent;
            with
              _ -> pad 1
          end;
          if nchildren < 1 then
            pr_string "{}"
          else
            pr_nth_child 0

      | L.Statement.For ->
          pr_string "for (";
          pb#open_box 0;
          let pr_semi_semi () = pr_semicolon(); pr_semicolon() in
          pr_selected ~fail_on_error ~otherwise:pr_semi_semi L.is_forhead children;
          pr_rparen();
          pb#close_box();
          if nchildren > 0 then begin
            let last = children.(nchildren - 1) in
            begin
              try
                let lab = getlab last in
                if L.is_block lab then
                  pad 1
                else if L.is_statement lab then
                  pr_break 1 pb#indent
                else
                  pad 1
              with
                _ -> pad 1
            end;
            pr_selected ~fail_on_error ~blk_style L.is_statement_or_block children
          end

      | L.Statement.ForEnhanced ->
          pr_string "for ("; pr_nth_child 0; pr_string " : "; pr_nth_child 1; pr_rparen();
          begin
            try
              if L.is_block (getlab (children.(2))) then
                pad 1
              else
                pr_break 1 pb#indent;
            with
              _ -> pad 1
          end;
          pr_nth_child 2

      | L.Statement.While ->
          pr_string "while ("; pr_nth_child 0; pr_rparen();
          begin
            try
              if L.is_block (getlab (children.(1))) then
                pad 1
              else
                pr_break 1 pb#indent;
            with
              _ -> pad 1
          end;
          pr_nth_child 1

      | L.Statement.Do ->
          pr_string "do "; pr_nth_child 0;
          pr_string " while ("; pr_nth_child 1; pr_rparen(); pr_semicolon()

      | L.Statement.Try ->
          pr_string "try ";
          pr_selected ~fail_on_error ~tail:pad1 L.is_resource_spec children;
          pr_selected ~fail_on_error ~tail:pad1 L.is_block children;
          pr_selected ~fail_on_error ~tail:pad1 L.is_catch_clause children;
          pr_selected ~fail_on_error ~tail:pad1 L.is_finally children

      | L.Statement.Yield -> pr_string "yield "; pr_nth_child 0; pr_semicolon()

      | L.Statement.Switch ->
          pr_string "switch ("; pr_nth_child 0; pr_rparen();
          begin
            try
              if L.is_switchblock (getlab (children.(1))) then
                pad 1
              else
                pr_break 1 pb#indent;
            with
              _ -> pad 1
          end;
          pr_nth_child 1

      | L.Statement.Synchronized ->
          pr_string "synchronized ("; pr_nth_child 0; pr_rparen();
          begin
            try
              if L.is_block (getlab (children.(1))) then
                pad 1
              else
                pr_break 1 pb#indent;
            with
              _ -> pad 1
          end;
          pr_nth_child 1

      | L.Statement.Return ->
          if nchildren = 0 then
            pr_string "return;"
          else begin
            pr_string "return "; pr_nth_child 0; pr_semicolon()
          end

      | L.Statement.Throw -> pr_string "throw "; pr_nth_child 0; pr_semicolon()

      | L.Statement.Break i_opt -> begin
          match i_opt with
	  | None -> pr_string "break;"
          | Some i -> pr_string "break "; pr_id i; pr_semicolon()
      end
      | L.Statement.Continue i_opt -> begin
          match i_opt with
	  | None -> pr_string "continue;"
          | Some i -> pr_string "continue "; pr_id i; pr_semicolon()
      end
      | L.Statement.Labeled i -> pr_id i; pr_string ": "; pr_nth_child 0

      | L.Statement.Expression(e, _) ->
          pr_expression ~fail_on_error ~prec e children; pr_semicolon()
  end

  | L.LocalVariableDeclaration(isstmt, _) ->
      pb#open_box 0;
      pr_selected ~fail_on_error L.is_modifiers children;
      pr_selected ~fail_on_error ~tail:pr_space L.is_type children;
      pr_selected ~fail_on_error ~sep:pr_comma L.is_variabledeclarator children;
      if isstmt then begin
        pr_semicolon()
      end;
      pb#close_box()

  | L.VariableDeclarator(i, dims) ->
      pr_id i; pr_dims dims;
      if nchildren > 0 then begin
        pr_string " ="; pr_break 1 pb#indent;
        pr_selected ~fail_on_error L.is_expression children;
        pr_selected ~fail_on_error L.is_arrayinitializer children
      end


and pr_selected
    ?(fail_on_error=true)
    ?(pra=pb#pr_a)
    ?(sep=pr_none)
    ?(head=pr_none)
    ?(tail=pr_none)
    ?(otherwise=pr_none)
    ?(blk_style=BSshort)
    ?(prec=0)
    filt a
    =
  let a' = find_nodes filt a in
  let present = (Array.length a') > 0 in
  if present then begin
    head();
    pra sep (pr_node ~fail_on_error ~blk_style ~prec) a';
    tail()
  end
  else
    otherwise()

and pr_types ?(fail_on_error=true) children =
  pb#pr_hova pr_comma (pr_node ~fail_on_error) children

and pr_dims dims = pr_string (dims_to_string dims)

and pr_expressions ?(fail_on_error=true) pr_sep children =
  pb#pr_hova pr_sep (pr_node ~fail_on_error) children

and pr_arguments ?(fail_on_error=true) children =
  pr_lparen(); pr_selected ~fail_on_error L.is_arguments children; pr_rparen()

and pr_parameters ?(fail_on_error=true) children =
  pr_lparen(); pr_selected ~fail_on_error L.is_parameters children; pr_rparen()

and pr_typeparameters ?(fail_on_error=true) children =
  pr_selected ~fail_on_error ~tail:pr_space L.is_typeparameters children

and pr_typearguments ?(fail_on_error=true) ?(nth=1) children =
  pr_selected ~fail_on_error (L.is_typearguments ~nth) children


and dims_to_string dims = if dims = 0 then "" else "[]"^(dims_to_string (dims - 1))

and get_specs children =
  let a = find_nodes L.is_specifier children in
  if Array.length a = 0 then
    [||]
  else
    (a.(0))#initial_children

and type_to_string ?(va=false) = function
  | L.Type.Byte               -> "byte"
  | L.Type.Short              -> "short"
  | L.Type.Int                -> "int"
  | L.Type.Long               -> "long"
  | L.Type.Char               -> "char"
  | L.Type.Float              -> "float"
  | L.Type.Double             -> "double"
  | L.Type.Boolean            -> "boolean"
  | L.Type.ClassOrInterface n
  | L.Type.Class n
  | L.Type.Interface n        -> norm_fqn n
  | L.Type.Array(ty, dims) when va && dims = 1 -> type_to_string ty
  | L.Type.Array(ty, dims) when va -> (type_to_string ty)^(dims_to_string (dims-1))
  | L.Type.Array(ty, dims) -> (type_to_string ty)^(dims_to_string dims)
  | L.Type.Void               -> "void"

and pr_primary ?(fail_on_error=true) ?(prec=0) p children =
  ignore prec;

  let nchildren = Array.length children in

  let pr_cc() = pr_string "::" in

  let pr_nth_child =
    if fail_on_error then
      fun ?(prec=0) nth -> pr_node ~fail_on_error:true ~prec children.(nth)
    else
      fun ?(prec=0) nth ->
        try
          pr_node ~fail_on_error:false ~prec children.(nth)
        with
          _ -> pr_string error_symbol
  in

  match p with
  | L.Primary.Name n when nchildren = 0 -> pr_name (norm_fqn n)

  | L.Primary.Name n ->
      pr_nth_child ~prec:(get_prec_of_sym ".") 0;
      pr_dot();
      pr_name (get_last_id n)(*(norm_fqn n)*)(* !!! *)

  | L.Primary.This -> pr_string "this"

  | L.Primary.Literal lit -> begin
      let s =
        match lit with
        | L.Literal.Integer i       -> i
        | L.Literal.FloatingPoint f -> f
        | L.Literal.True            -> "true"
        | L.Literal.False           -> "false"
        | L.Literal.Character c     -> "'"^c^"'"
        | L.Literal.String s        -> "\""^s^"\""
        | L.Literal.TextBlock s     -> "\"\"\""^s^"\"\"\""
        | L.Literal.Null            -> "null"
      in
      pr_string s
  end

  | L.Primary.ClassLiteral     -> pr_nth_child 0; pr_string ".class"
  | L.Primary.ClassLiteralVoid -> pr_string "void.class"
  | L.Primary.QualifiedThis n  -> pr_name n; pr_string ".this"

  | L.Primary.InstanceCreation _ ->
      pb#open_vbox 0;
      pb#open_box pb#indent;
      pr_string "new ";
      pr_typearguments ~fail_on_error children;
      pr_selected ~fail_on_error L.is_type children;
      pr_arguments ~fail_on_error children;
      pb#close_box();
      pr_selected ~fail_on_error L.is_classbody children;
      pb#close_box()

  | L.Primary.QualifiedInstanceCreation i ->
      pr_selected ~fail_on_error ~prec:(get_prec_of_sym ".") L.is_primary children;
      pr_string ".new ";
      pr_typearguments ~fail_on_error children;
      pr_id i;
      pr_typearguments ~fail_on_error ~nth:2 children;
      pr_arguments ~fail_on_error children;
      pr_selected ~fail_on_error L.is_classbody children

  | L.Primary.NameQualifiedInstanceCreation(n, i) ->
      pr_name n;
      pr_string ".new ";
      pr_typearguments ~fail_on_error children;
      pr_id i;
      pr_typearguments ~fail_on_error ~nth:2 children;
      pr_arguments ~fail_on_error children;
      pr_selected ~fail_on_error L.is_classbody children

  | L.Primary.FieldAccess i ->
      if nchildren > 0 then begin
        pr_nth_child ~prec:(get_prec_of_sym ".") 0; pr_dot()
      end;
      pr_id i

  | L.Primary.SuperFieldAccess i -> pr_string "super."; pr_id i

  | L.Primary.ClassSuperFieldAccess i ->
      pr_nth_child 0; pr_string ".super."; pr_id i

  | L.Primary.SimpleMethodInvocation i ->
      pb#open_box pb#indent;
      pr_selected ~fail_on_error L.is_qualifier children; pr_id (undeco i);
      pr_arguments ~fail_on_error children;
      pb#close_box()

  | L.Primary.PrimaryMethodInvocation i ->
      pb#open_box pb#indent;
      pr_selected ~fail_on_error ~prec:(get_prec_of_sym ".") L.is_primary children; pr_dot();
      pr_typearguments ~fail_on_error children;
      pr_id (undeco i); pr_arguments ~fail_on_error children;
      pb#close_box()

  | L.Primary.AmbiguousMethodInvocation i ->
      pb#open_box pb#indent;
      pr_selected ~fail_on_error ~prec:(get_prec_of_sym ".") L.is_primary children; pr_dot();
      pr_typearguments ~fail_on_error children;
      pr_id (undeco i); pr_arguments ~fail_on_error children;
      pb#close_box()

  | L.Primary.TypeMethodInvocation(n, i) ->
      pb#open_box pb#indent;
      pr_name (norm_fqn n); pr_dot(); pr_typearguments ~fail_on_error children;
      pr_id (undeco i); pr_arguments ~fail_on_error children;
      pb#close_box()

  | L.Primary.SuperMethodInvocation i ->
      pb#open_box pb#indent;
      pr_string "super."; pr_typearguments ~fail_on_error children;
      pr_id (undeco i); pr_arguments ~fail_on_error children;
      pb#close_box()

  | L.Primary.ClassSuperMethodInvocation i ->
      pb#open_box pb#indent;
      pr_selected ~fail_on_error L.is_type children;
      pr_string ".super."; pr_typearguments ~fail_on_error children;
      pr_id (undeco i); pr_arguments ~fail_on_error children;
      pb#close_box()

  | L.Primary.ArrayAccess ->
      pr_nth_child ~prec:(get_prec_of_sym "[]") 0;
      pr_string "["; pr_nth_child 1; pr_string "]"

  | L.Primary.ArrayCreationDims dims ->
      pr_string "new "; pr_nth_child 0; pr_string "[";
      let rest = Array.sub children 1 (nchildren-1) in
      pb#pr_hova (fun () -> pr_string "][") (pr_node ~fail_on_error) rest;
      pr_string "]";
      pr_dims dims

  | L.Primary.ArrayCreationInit ->
      pr_string "new "; pr_nth_child 0;
      if nchildren > 1 then begin
        pr_nth_child 1
      end

  | L.Primary.Paren _ -> pr_lparen(); pr_nth_child 0; pr_rparen()

  | L.Primary.NameMethodReference(n, i) ->
      pb#open_box pb#indent;
      pr_name n; pr_cc(); pr_typearguments ~fail_on_error children; pr_id i;
      pb#close_box()

  | L.Primary.PrimaryMethodReference i ->
      pb#open_box pb#indent;
      pr_selected ~fail_on_error ~prec:(get_prec_of_sym "::") L.is_primary children; pr_cc();
      pr_typearguments ~fail_on_error children; pr_id i;
      pb#close_box()

  | L.Primary.SuperMethodReference i ->
      pb#open_box pb#indent;
      pr_string "super"; pr_cc(); pr_typearguments ~fail_on_error children; pr_id i;
      pb#close_box()

  | L.Primary.TypeSuperMethodReference(n, i) ->
      pb#open_box pb#indent;
      pr_name n; pr_string ".super"; pr_cc();
      pr_typearguments ~fail_on_error children; pr_id i;
      pb#close_box()

  | L.Primary.TypeNewMethodReference _ ->
      pb#open_box pb#indent;
      pr_selected ~fail_on_error L.is_type children;
      pr_cc(); pr_typearguments ~fail_on_error children; pr_string "new";
      pb#close_box()

  | L.Primary.AmbiguousName n when nchildren = 0 -> (*pr_name (norm_fqn n)*)pr_id (get_last_id n)

  | L.Primary.AmbiguousName n ->
      pr_nth_child ~prec:(get_prec_of_sym ".") 0;
      pr_dot();
      pr_id (get_last_id n)(* !!! *)

and pr_expression ?(fail_on_error=true) ?(prec=0) e children =
  let prec' = get_prec_of_expression e in
  let pr_nth_child =
    if fail_on_error then
      fun ?(prec=0) nth -> pr_node ~fail_on_error:true ~prec children.(nth)
    else
      fun ?(prec=0) nth ->
        try
          pr_node ~fail_on_error:false ~prec children.(nth)
        with
          _ -> pr_string error_symbol
  in
  match e with
  | L.Expression.Primary p -> pr_primary ~fail_on_error ~prec p children

  | L.Expression.UnaryOperator uop -> begin
      match uop with
      | L.UnaryOperator.PostIncrement -> pr_nth_child ~prec:prec' 0; pr_string "++"
      | L.UnaryOperator.PostDecrement -> pr_nth_child ~prec:prec' 0; pr_string "--"
      | L.UnaryOperator.PreIncrement  -> pr_string "++"; pr_nth_child ~prec:prec' 0
      | L.UnaryOperator.PreDecrement  -> pr_string "--"; pr_nth_child ~prec:prec' 0
      | L.UnaryOperator.Positive      -> pr_string "+"; pr_nth_child ~prec:prec' 0
      | L.UnaryOperator.Negative      -> pr_string "-"; pr_nth_child ~prec:prec' 0
      | L.UnaryOperator.Complement    -> pr_string "~"; pr_nth_child ~prec:prec' 0
      | L.UnaryOperator.Not           -> pr_string "!"; pr_nth_child ~prec:prec' 0
  end

  | L.Expression.BinaryOperator bop -> begin
      let s =
        match bop with
        | L.BinaryOperator.Mul     -> "*"
        | L.BinaryOperator.Div     -> "/"
        | L.BinaryOperator.Mod     -> "%"
        | L.BinaryOperator.Add     -> "+"
        | L.BinaryOperator.Sub     -> "-"
        | L.BinaryOperator.ShiftL  -> "<<"
        | L.BinaryOperator.ShiftR  -> ">>"
        | L.BinaryOperator.ShiftRU -> ">>>"
        | L.BinaryOperator.Eq      -> "=="
        | L.BinaryOperator.Neq     -> "!="
        | L.BinaryOperator.Lt      -> "<"
        | L.BinaryOperator.Gt      -> ">"
        | L.BinaryOperator.Le      -> "<="
        | L.BinaryOperator.Ge      -> ">="
        | L.BinaryOperator.BitAnd  -> "&"
        | L.BinaryOperator.BitOr   -> "|"
        | L.BinaryOperator.BitXor  -> "^"
        | L.BinaryOperator.And     -> "&&"
        | L.BinaryOperator.Or      -> "||"
      in
      pr_nth_child ~prec:prec' 0;
      pad 1; pr_string s; pad 1;
      pr_nth_child ~prec:prec' 1
  end

  | L.Expression.AssignmentOperator(aop, _) -> begin
      let s =
        match aop with
        | L.AssignmentOperator.Eq        -> "="
        | L.AssignmentOperator.MulEq     -> "*="
        | L.AssignmentOperator.DivEq     -> "/="
        | L.AssignmentOperator.ModEq     -> "%="
        | L.AssignmentOperator.AddEq     -> "+="
        | L.AssignmentOperator.SubEq     -> "-="
        | L.AssignmentOperator.ShiftLEq  -> "<<="
        | L.AssignmentOperator.ShiftREq  -> ">>="
        | L.AssignmentOperator.ShiftRUEq -> ">>>="
        | L.AssignmentOperator.AndEq     -> "&="
        | L.AssignmentOperator.XorEq     -> "^="
        | L.AssignmentOperator.OrEq      -> "|="
      in
      pb#open_box 0;
      pr_nth_child 0; pad 1;
      pr_string s; pr_space();
      pr_nth_child ~prec:prec_of_assignment_operators 1;
      pb#close_box()
  end

  | L.Expression.Cast ->
      pr_lparen(); pr_nth_child 0; pr_rparen(); pr_nth_child ~prec:prec' 1

  | L.Expression.Instanceof ->
      pr_nth_child ~prec:prec' 0; pr_string " instanceof "; pr_nth_child 1

  | L.Expression.Cond ->
      pr_nth_child ~prec:prec' 0; pr_string " ? ";
      pr_nth_child ~prec:prec' 1; pr_string " : ";
      pr_nth_child ~prec:prec' 2

  | L.Expression.Lambda -> begin
      begin
        let c0 = children.(0) in
        match getlab c0 with
        | L.InferredFormalParameter i -> pr_id i
        | L.InferredFormalParameters -> begin
            let pr_ifp n =
              match getlab n with
              | L.InferredFormalParameter i -> pr_id i
              | _ -> pr_string error_symbol
            in
            pr_lparen();
            pb#pr_hova pr_comma pr_ifp c0#initial_children;
            pr_rparen()
        end
        | L.Parameters _ -> pr_parameters ~fail_on_error children
        | _ -> pr_string error_symbol
      end;
      pr_string " -> "; pr_nth_child 1
  end

  | L.Expression.Switch -> begin
      pr_string "switch ("; pr_nth_child 0; pr_rparen();
      begin
        try
          if L.is_switchblock (getlab (children.(1))) then
            pad 1
          else
            pr_break 1 pb#indent;
        with
          _ -> pad 1
      end;
      pr_nth_child 1
  end

  | L.Expression.NaryAdd -> pb#pr_a (fun () -> pr_string " + ") (pr_node ~fail_on_error) children



let unparse ?(no_boxing=false) ?(no_header=false) ?(fail_on_error=true) t =
  let prev_boxing_flag = pb#boxing_flag in
  if no_boxing && prev_boxing_flag then begin
    Format.open_hbox();
    pb#disable_boxing()
  end;

  pb#open_box 0;
  if not no_header then begin
    pr_string "// generated by Diff/AST Java Unparser"; force_newline()
  end;
  if not fail_on_error && not no_header then begin
    pr_string (Printf.sprintf "// error_symbol=\"%s\"" error_symbol); force_newline();
  end;
  pr_node ~fail_on_error t;
  pb#close_box();
  pr_flush();

  if no_boxing && prev_boxing_flag then begin
    pb#enable_boxing();
    Format.close_box()
  end
