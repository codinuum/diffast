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
 * AST for the Java Language
 *
 * ast.ml
 *
 *)

[%%prepare_logger]

open Printf

module Ast_base = Langs_common.Ast_base
module Loc = Langs_common.Astloc

type loc = Loc.t

type identifier = string

type simple_name = identifier

type dims = int (* dimension *)

type expr_kind = EKunknown | EKfacc | EKname

type identifier_attribute =
  | IApackage
  | IAclass of string
  | IAinterface of string
  | IAtypename of string
  | IAmethod
  | IAfield
  | IAconstructor
  | IAparameter
  | IAvariable
  | IAlabel
  | IAstatic of string
  | IAtypeparameter
  | IAexpression of expr_kind
  | IAarray

let expr_kind_to_str = function
  | EKunknown -> "unknown"
  | EKfacc -> "facc"
  | EKname -> "name"

let iattr_to_str = function
  | IApackage     -> "package"
  | IAclass s     -> "class"^(if s = "" then "" else ":"^s)
  | IAinterface s -> "interface"^(if s = "" then "" else ":"^s)
  | IAtypename s  -> "typename"^(if s = "" then "" else ":"^s)
  | IAmethod      -> "method"
  | IAconstructor -> "constructor"
  | IAlabel       -> "label"
  | IAfield       -> "field"
  | IAparameter   -> "parameter"
  | IAvariable    -> "variable"
  | IAstatic s    -> "static member"^(if s = "" then "" else ":"^s)
  | IAtypeparameter -> "type parameter"
  | IAexpression ek -> "expression:"^(expr_kind_to_str ek)
  | IAarray -> "array"


type frame_kind =
  | FKclass of string * bool(* has_super *)ref
  | FKtypeparameter
  | FKmethod of string * bool(* is_static *)ref
  | FKother

let frame_kind_to_string = function
  | FKclass(s, x) -> sprintf "class:%s:has_super=%B" s !x
  | FKtypeparameter -> "typeparameter"
  | FKmethod(s, x) -> sprintf "method:%s:is_static=%B" s !x
  | FKother -> "other"

let is_class_frame = function
  | FKclass _ -> true
  | _ -> false

let is_method_frame = function
  | FKmethod _ -> true
  | _ -> false

class frame kind = object (self)
  val tbl = (Hashtbl.create 0 : (string, identifier_attribute) Hashtbl.t)

  val qtbl = (Hashtbl.create 0 : (string, identifier_attribute) Hashtbl.t)

  method kind = kind

  method is_typeparameter_frame = kind = FKtypeparameter
  method is_class_frame = is_class_frame kind
  method is_method_frame = is_method_frame kind

  method get_class_name =
    match kind with
    | FKclass(n, _) -> n
    | _ -> raise Not_found

  method get_method_name =
    match kind with
    | FKmethod(n, _) -> n
    | _ -> raise Not_found

  method private _add t id attr =
    if not (List.mem attr (Hashtbl.find_all t id)) then
      Hashtbl.add t id attr

  method find id =
    Hashtbl.find tbl id

  method add id attr =
    self#_add tbl id attr

  method find_all id =
    Hashtbl.find_all tbl id


  method qfind qn =
    Hashtbl.find qtbl qn

  method qadd qn attr =
    self#_add qtbl qn attr

  method qfind_all qn =
    Hashtbl.find_all qtbl qn


  method iter f =
    Hashtbl.iter f tbl

  method to_string =
    sprintf "FRAME[%s]:\nIDENT:{%s}\nQNAME:{%s}\n"
      (frame_kind_to_string kind)
      (Hashtbl.fold (fun id _ s -> id^";"^s) tbl "")
      (Hashtbl.fold (fun qn _ s -> qn^";"^s) qtbl "")

end

type resolve_result =
  | R_resolved of string
  | R_deferred of string * frame Stack.t * string

let resolve_result_to_str = function
  | R_resolved s -> s
  | R_deferred(id, _, s) -> sprintf "{DEFERRED:%s?%s}" id s

let mkresolved s = R_resolved s

let is_resolved = function
  | R_resolved _ -> true
  | _ -> false

let is_inner lname =
  String.contains lname '$'

let split_inner lname = (* parent * rest *)
  let idx = String.index lname '$' in
  String.sub lname 0 idx, String.sub lname idx ((String.length lname) - idx)

type name_attribute =
  | NApackage
  | NAtype of resolve_result
  | NAexpression of expr_kind
  | NAmethod
  | NApackageOrType
  | NAstatic of resolve_result
  | NAambiguous of resolve_result
  | NAunknown

let is_expr_attr = function
  | NAexpression _ -> true
  | _ -> false

let iattr_to_nattr = function
  | IApackage     -> NApackage
  | IAmethod      -> NAmethod
  | IAexpression ek -> NAexpression ek
  | _ -> failwith "Ast.iattr_to_nattr"

let get_resolved_name = function
  | NAtype (R_resolved s)
  | NAstatic (R_resolved s) ->
      if s = "" then
        raise Not_found
      else
        s
  | _ -> raise Not_found

let set1 orig a =
  match !orig with
  | NApackageOrType -> begin
      match a with
      | NApackage | NAtype _ -> orig := a
      | _ -> ()
  end
  | NAexpression _ -> begin
      match a with
      | NAstatic _ -> orig := a
      | _ -> ()
  end
  | NAambiguous _ -> begin
      match a with
      | NAunknown | NAambiguous _ -> ()
      | _ -> orig := a
  end
  | NAunknown -> orig := a
  | _ -> ()

let is_capitalized s =
  try
    let c = Char.code s.[0] in
    65 <= c && c <= 90
  with
    _ -> false

let is_all_capitalized s =
  try
    let c = Char.code s.[0] in
    65 <= c && c <= 90 &&
    String.for_all
      (fun chr ->
        let c = Char.code chr in
        65 <= c && c <= 90 ||
        48 <= c && c <= 57 ||
        chr = '_'
      ) s
  with
    _ -> false

type literal =
  | Linteger of string
  | LfloatingPoint of string
  | Ltrue
  | Lfalse
  | Lcharacter of string
  | Lstring of string
  | LtextBlock of string
  | Lnull

type assignment_operator = { ao_desc : assignment_operator_desc; ao_loc : loc; }
and assignment_operator_desc =
  | AOeq
  | AOmulEq
  | AOdivEq
  | AOmodEq
  | AOaddEq
  | AOsubEq
  | AOshiftLEq
  | AOshiftREq
  | AOshiftRUEq
  | AOandEq
  | AOxorEq
  | AOorEq

type unary_operator =
  | UOpostIncrement
  | UOpostDecrement
  | UOpreIncrement
  | UOpreDecrement
  | UOpositive
  | UOnegative
  | UOcomplement
  | UOnot

type binary_operator =
  | BOmul | BOdiv | BOmod | BOadd | BOsub | BOshiftL | BOshiftR | BOshiftRU
  | BOeq | BOneq | BOlt | BOgt | BOle | BOge
  | BObitAnd | BObitOr | BObitXor | BOand | BOor

type name = { n_desc : name_desc; n_loc : loc; }
and name_desc =
  | Nsimple of name_attribute ref * identifier
  | Nqualified of name_attribute ref * name * annotation list * identifier
  | Nerror of string

and javatype = { ty_desc : javatype_desc; ty_loc : loc; }

and primitive_type =
  | PTbyte | PTshort | PTint | PTlong
  | PTchar
  | PTfloat | PTdouble
  | PTboolean

and javatype_desc =
  | Tprimitive of annotation list * primitive_type

  | TclassOrInterface of type_spec list
  | Tclass of type_spec list
  | Tinterface of type_spec list

  | Tarray of javatype (* other than array *) * annot_dim list

  | Tvoid (* not a type (only for convenience) *)

and type_spec =
  | TSname of annotation list * name
  | TSapply of annotation list * name * type_arguments

and type_argument = { ta_desc : type_argument_desc; ta_loc : loc; }
and type_argument_desc =
  | TAreferenceType of javatype
  | TAwildcard of wildcard

and wildcard_bounds = { wb_desc : wildcard_bounds_desc; wb_loc : loc; }
and wildcard_bounds_desc =
  | WBextends of javatype
  | WBsuper of javatype

and wildcard = annotation list * wildcard_bounds option

and type_arguments = { tas_type_arguments : type_argument list; tas_loc : loc; }

and variable_declarator_id = (loc * identifier) * annot_dim list

and throws = { th_exceptions : javatype list;
	       th_loc        : loc;
	      }

and extends_class = { exc_class : javatype;
		      exc_loc   : loc
		     }
and extends_interfaces = { exi_interfaces : javatype list;
			   exi_loc        : loc;
			  }

and implements = { im_interfaces : javatype list;
		   im_loc        : loc;
		  }

and permits = { pm_type_names : name list;
		pm_loc    : loc;
	      }

and formal_parameter =
    { fp_modifiers              : modifiers option;
      fp_type                   : javatype;
      fp_variable_declarator_id : variable_declarator_id;
      fp_variable_arity         : bool;
      fp_loc                    : loc;
      fp_receiver               : identifier option;
    }

and modifiers = { ms_modifiers : modifier list; ms_loc : loc; }

and modifier = { m_desc : modifier_desc; m_loc : loc; }
and modifier_desc =
  | Mpublic
  | Mprotected
  | Mprivate
  | Mstatic
  | Mabstract
  | Mfinal
  | Mnative
  | Msynchronized
  | Mtransient
  | Mvolatile
  | Mstrictfp
  | Mannotation of annotation
  | Mdefault
  | Mtransitive
  | Msealed
  | Mnon_sealed
  | Merror of string

and variable_initializer = { vi_desc : variable_initializer_desc; vi_loc : loc; }
and variable_initializer_desc =
  | VIexpression of expression
  | VIarray of array_initializer
  | VIerror of string

and array_initializer = variable_initializer list

and variable_declarator =
    { vd_variable_declarator_id : variable_declarator_id;
      vd_variable_initializer   : variable_initializer option;
      vd_is_local               : bool ref;
      vd_loc                    : loc;
    }

and variable_declarators = variable_declarator list

and class_declaration_head = {
    ch_modifiers       : modifiers option;
    ch_identifier      : identifier;
    ch_identifier_loc  : loc;
    ch_type_parameters : type_parameters option;
    ch_extends_class   : extends_class option;
    ch_implements      : implements option;
    ch_permits         : permits option;
    ch_loc             : loc;
  }

and record_declaration_head = {
    rh_modifiers       : modifiers option;
    rh_identifier      : identifier;
    rh_identifier_loc  : loc;
    rh_type_parameters : type_parameters option;
    rh_record_header   : formal_parameter list;
    rh_implements      : implements option;
    rh_loc             : loc;
  }

and module_declaration = {
    mod_head : module_declaration_head;
    mod_body : module_body;
    mod_loc  : loc;
  }

and module_declaration_head = {
    mdh_annotations : annotation list;
    mdh_open        : loc option;
    mdh_name        : name;
    mdh_loc         : loc;
  }

and module_name = { mn_name : name; mn_loc : loc }

and module_body = { mb_module_directives : module_directive list; mb_loc : loc }

and module_directive = { md_desc : module_directive_desc; md_loc : loc }

and module_directive_desc =
  | MDrequires of modifier list * name
  | MDexports of name * module_name list
  | MDopens of name * module_name list
  | MDuses of name
  | MDprovides of name * module_name list

and class_declaration = { cd_desc : class_declaration_desc; cd_loc : loc; }

and class_declaration_desc =
  | CDclass of class_declaration_head * class_body
  | CDenum  of class_declaration_head * enum_body
  | CDrecord of record_declaration_head * record_body
  | CDaspect of class_declaration_head * aspect_body

and type_parameters = { tps_type_parameters : type_parameter list;
			tps_loc             : loc;
		      }

and type_variable = identifier

and type_parameter = { tp_type_variable : type_variable;
                       tp_annotations   : annotation list;
		       tp_type_bound    : type_bound option;
		       tp_loc           : loc;
		     }

and type_bound = { tb_reference_type    : javatype;
		   tb_additional_bounds : additional_bound list;
		   tb_loc               : loc;
		 }
and additional_bound = { ab_interface : javatype; ab_loc : loc; }

and enum_body = { eb_enum_constants          : enum_constant list;
		  eb_class_body_declarations : class_body_declaration list;
		  eb_loc                     : loc;
		}

and enum_constant = { ec_annotations : annotations;
		      ec_identifier  : identifier;
		      ec_arguments   : arguments option;
		      ec_class_body  : class_body option;
		      ec_loc         : loc;
		    }

and class_body =
    { cb_class_body_declarations : class_body_declaration list;
      cb_loc                     : loc;
    }

and class_body_declaration = { cbd_desc : class_body_declaration_desc;
			       cbd_loc  : loc;
			     }

and class_body_declaration_desc =
  | CBDfield of field_declaration
  | CBDmethod of method_header * block option
  | CBDclass of class_declaration
  | CBDinterface of interface_declaration
  | CBDstaticInitializer of block
  | CBDinstanceInitializer of block
  | CBDconstructor of constructor_declaration
  | CBDempty
  | CBDerror of string
  | CBDpointcut of pointcut_declaration
  | CBDdeclare of declare_declaration

and record_body =
    { rb_record_body_declarations : record_body_declaration list;
      rb_loc                      : loc;
    }

and record_body_declaration = { rbd_desc : record_body_declaration_desc;
			        rbd_loc  : loc;
			      }

and record_body_declaration_desc =
  | RBDclass_body_decl of class_body_declaration
  | RBDcompact_ctor_decl of compact_constructor_declaration

and declare_declaration = { dd_desc : declare_declaration_desc;
                            dd_loc  : loc;
                          }

and declare_declaration_desc =
  | DDparents of string * classname_pattern_expr * extends_class option * implements option
  | DDmessage of string * pointcut_expr * primary
  | DDsoft of string * pointcut_expr
  | DDprecedence of string * classname_pattern_expr list

and pointcut_declaration = { pcd_modifiers       : modifiers option;
                             pcd_name            : identifier;
                             pcd_parameters_loc  : loc;
                             pcd_parameters      : formal_parameter list;
                             pcd_pointcut_expr   : pointcut_expr option;
                             pcd_loc             : loc;
                           }

and pointcut_expr = { pe_desc : pointcut_expr_desc;
                      pe_loc  : loc;
                    }

and pointcut_expr_desc =
  | PEand of pointcut_expr * pointcut_expr
  | PEor of pointcut_expr * pointcut_expr
  | PEnot of pointcut_expr
  | PEparen of pointcut_expr
  | PEwithin of classname_pattern_expr

and classname_pattern_expr = { cpe_desc : classname_pattern_expr_desc;
                               cpe_loc  : loc;
                             }

and classname_pattern_expr_desc =
  | CPEand of classname_pattern_expr * classname_pattern_expr
  | CPEor of classname_pattern_expr * classname_pattern_expr
  | CPEnot of classname_pattern_expr
  | CPEparen of classname_pattern_expr
  | CPEname of string
  | CPEnamePlus of string

and field_declaration = { fd_modifiers            : modifiers option;
			  fd_type                 : javatype;
			  fd_variable_declarators : variable_declarators;
			  fd_loc                  : loc;
			}

and method_header = { mh_modifiers       : modifiers option;
		      mh_type_parameters : type_parameters option;
                      mh_annotations     : annotation list;
		      mh_return_type     : javatype;
		      mh_name            : identifier;
		      mh_name_loc        : loc;
		      mh_parameters_loc  : loc;
		      mh_parameters      : formal_parameter list;
		      mh_dims            : annot_dim list;
		      mh_throws          : throws option;
		      mh_loc             : loc;
		    }

and constructor_declaration = { cnd_modifiers       : modifiers option;
				cnd_type_parameters : type_parameters option;
				cnd_name            : simple_name;
				cnd_parameters_loc  : loc;
				cnd_parameters      : formal_parameter list;
				cnd_throws          : throws option;
				cnd_body            : constructor_body;
				cnd_loc             : loc;
			      }

and compact_constructor_declaration = { ccnd_modifiers       : modifiers option;
				        ccnd_name            : identifier;
				        ccnd_body            : constructor_body;
				        ccnd_loc             : loc;
			              }

and constructor_body =
    { cnb_explicit_constructor_invocation : explicit_constructor_invocation option;
      cnb_block                           : block_statement list;
      cnb_loc                             : loc;
    }

and arguments = { as_arguments : argument list; as_loc : loc; }

and explicit_constructor_invocation =
    { eci_desc : explicit_constructor_invocation_desc;
      eci_loc  : loc
    }
and explicit_constructor_invocation_desc =
  | ECIthis of type_arguments option * arguments
  | ECIsuper of type_arguments option * arguments
  | ECIprimary of primary * type_arguments option * arguments
  | ECIname of name * type_arguments option * arguments
  | ECIerror of string

and interface_declaration_head = {
    ifh_modifiers          : modifiers option;
    ifh_identifier         : identifier;
    ifh_type_parameters    : type_parameters option;
    ifh_extends_interfaces : extends_interfaces option;
    ifh_permits            : permits option;
    ifh_loc                : loc;
  }

and interface_declaration = { ifd_desc : interface_declaration_desc;
			      ifd_loc  : loc; }

and interface_declaration_desc =
  | IFDnormal of interface_declaration_head * interface_body
  | IFDannotation of interface_declaration_head	* annotation_type_body

and annotation_type_body =
    { atb_member_declarations : annotation_type_member_declaration list;
      atb_loc                 : loc;
    }

and constant_declaration = field_declaration

and default_value = element_value

and annotation_type_member_declaration =
    { atmd_desc : annotation_type_member_declaration_desc;
      atmd_loc  : loc;
    }
and annotation_type_member_declaration_desc =
  | ATMDconstant of constant_declaration
  | ATMDelement of
      modifiers option *
	javatype *
	identifier *
        annot_dim list *
	default_value option

  | ATMDclass of class_declaration
  | ATMDinterface of interface_declaration
  | ATMDempty

and annot_dim = { ad_annotations : annotations;
                  ad_loc         : loc;
                  ad_ellipsis    : bool;
                }

and interface_body = { ib_member_declarations : interface_member_declaration list;
		       ib_loc                 : loc;
		     }

and interface_method_declaration = { amd_method_header : method_header;
                                     amd_body          : block option;
				     amd_loc           : loc;
				  }

and interface_member_declaration =
    { imd_desc : interface_member_declaration_desc;
      imd_loc  : loc;
    }
and interface_member_declaration_desc =
  | IMDconstant of field_declaration
  | IMDinterfaceMethod of interface_method_declaration
  | IMDclass of class_declaration
  | IMDinterface of interface_declaration
  | IMDempty

and aspect_body =
        { abd_aspect_body_declarations : class_body_declaration list;
          abd_loc                      : loc;
        }

and block_statement = { bs_desc  : block_statement_desc;
			bs_loc   : loc;
		      }
and block_statement_desc =
  | BSlocal of local_variable_declaration
  | BSclass of class_declaration
  | BSstatement of statement
  | BSerror of string

and local_variable_declaration =
    { lvd_modifiers            : modifiers option;
      lvd_type                 : javatype;
      lvd_variable_declarators : variable_declarators;
      lvd_loc                  : loc;
    }


and block = { b_block_statements : block_statement list; b_loc : loc; }

and statement = { s_desc  : statement_desc;
		  s_loc   : loc;
                  s_extra_loc : loc option;
		}
and statement_desc =
  | Sblock of block
  | Sempty
  | Sexpression of statement_expression
  | Sswitch of expression * switch_block
  | Sdo of statement * expression
  | Sbreak of identifier option
  | Scontinue of identifier option
  | Sreturn of expression option
  | Ssynchronized of expression * block
  | Sthrow of expression
  | Stry of resource_spec option * block * catches option * finally option
  | Syield of expression

  | Slabeled of identifier * statement
  | SifThen of expression * statement
  | SifThenElse of expression * statement * statement
  | Swhile of expression * statement
  | Sfor of
      for_init option * expression option * statement_expression list
	* statement
  | SforEnhanced of formal_parameter * expression * statement
  | Sassert1 of expression
  | Sassert2 of expression * expression
  | Serror of string

and statement_expression = { se_desc : statement_expression_desc; se_loc : loc; }
and statement_expression_desc =
  | SEassignment of assignment
  | SEpreIncrement of expression
  | SEpreDecrement of expression
  | SEpostIncrement of expression
  | SEpostDecrement of expression
  | SEmethodInvocation of method_invocation
  | SEclassInstanceCreation of class_instance_creation
  | SEerror of string

and for_init = { fi_desc : for_init_desc; fi_loc : loc; }
and for_init_desc =
  | FIstatement of statement_expression list
  | FIlocal of local_variable_declaration

and primary = { mutable p_desc : primary_desc; p_loc : loc; }
and primary_desc =
  | Pname of name
  | Pliteral of literal
  | PclassLiteral of javatype
  | PclassLiteralVoid
  | Pthis
  | PqualifiedThis of name (* of type *)
  | Pparen of expression
  | PclassInstanceCreation of class_instance_creation
  | PfieldAccess of field_access
  | PmethodInvocation of method_invocation
  | ParrayAccess of array_access
  | ParrayCreationExpression of array_creation_expression
  | PmethodReference of method_reference
  | Perror of string

and method_reference = { mr_desc : method_reference_desc; mr_loc : loc; }
and method_reference_desc =
  | MRname of name * type_arguments option * identifier
  | MRprimary of primary * type_arguments option * identifier
  | MRsuper of type_arguments option * identifier
  | MRtypeSuper of name * type_arguments option * identifier
  | MRtypeNew of javatype * type_arguments option

and array_creation_expression =
  | ACEtype of javatype * dim_expr list * annot_dim list
  | ACEtypeInit of javatype * annot_dim list * array_initializer

and dim_expr = { de_desc : expression; de_loc : loc; }

and class_instance_creation = { cic_desc : class_instance_creation_desc;
				cic_loc  : loc;
			      }
and class_instance_creation_desc =
  | CICunqualified of
      type_arguments option *
	javatype *
	arguments *
	class_body option
  | CICqualified of
      primary *
	type_arguments option *
	identifier *
	type_arguments option *
	arguments *
	class_body option
  | CICnameQualified of
      name *
	type_arguments option *
	identifier *
	type_arguments option *
	arguments *
	class_body option


and field_access =
  | FAprimary of primary * identifier
  | FAsuper of identifier
  | FAclassSuper of name (* of type *) * identifier
  | FAimplicit of name(*identifier*)

and method_invocation = { mutable mi_desc : method_invocation_desc; mi_loc : loc; }
and method_invocation_desc =
  | MImethodName of name (* of method *) * arguments
  | MIprimary of primary * type_arguments option * identifier * arguments
  | MItypeName of name * type_arguments option * identifier * arguments
  | MIsuper of
      loc (* of super *) * type_arguments option * identifier * arguments
  | MIclassSuper of
      loc (* of class *) * loc (* of super *) *
      name (* of type *) * type_arguments option * identifier * arguments

and array_access = { aa_desc : array_access_desc; aa_loc : loc; }
and array_access_desc =
  | AAname of name (* of expression *) * expression
  | AAprimary of primary * expression

and argument = expression

and expression = { e_desc : expression_desc; e_loc : loc; }
and expression_desc =
  | Eprimary of primary
  | Eunary of unary_operator * expression
  | Ebinary of binary_operator * expression * expression
  | Ecast of javatype * expression
  | Einstanceof of expression * javatype
  | EinstanceofP of expression * local_variable_declaration
  | Econd of expression * expression * expression
  | Eassignment of assignment
  | Elambda of lambda_params * lambda_body
  | Eswitch of expression * switch_block
  | Eerror of string

and lambda_params = { lp_desc : lambda_params_desc; lp_loc : loc; }
and lambda_params_desc =
  | LPident of identifier
  | LPformal of formal_parameter list
  | LPinferred of (loc * identifier) list

and lambda_body = LBexpr of expression | LBblock of block

and annotation = { a_desc : annotation_desc; a_loc : loc; }
and annotation_desc =
  | Anormal of name * element_value_pair list
  | Amarker of name
  | AsingleElement of name * element_value

and annotations = annotation list

and element_value = { ev_desc : element_value_desc; ev_loc : loc; }
and element_value_desc =
  | EVconditional of expression
  | EVannotation of annotation
  | EVarrayInit of element_value list

and element_value_pair = { evp_desc : element_value_pair_desc; evp_loc : loc; }
and element_value_pair_desc = identifier * element_value

and assignment = left_hand_side * assignment_operator * expression

and left_hand_side = expression

and constant_expression = expression (* where ... *)

and switch_label_desc =
  | SLconstant of constant_expression list
  | SLdefault

and switch_label = { sl_desc : switch_label_desc; sl_loc : loc; }

and switch_block_stmt_grp = switch_label list * block_statement list

and switch_rule_label = { srl_desc : switch_label_desc; srl_loc : loc; }

and switch_rule = switch_rule_label * switch_rule_body

and switch_rule_body = { srb_desc : switch_rule_body_desc; srb_loc : loc; }
and switch_rule_body_desc =
  | SRBexpr of expression
  | SRBblock of block
  | SRBthrow of statement

and switch_block = { sb_switch_block_stmt_grps : switch_block_stmt_grp list;
                     sb_switch_rules           : switch_rule list;
                     sb_loc                    : loc;
                   }

and catch = { c_formal_parameter : catch_formal_parameter;
	      c_block            : block;
	      c_loc              : loc;
	    }

and catches = catch list

and finally = { f_block : block;
		f_loc   : loc;
	      }

and catch_formal_parameter =
        { cfp_modifiers              : modifiers option;
          cfp_type_list              : javatype list;
          cfp_variable_declarator_id : variable_declarator_id;
          cfp_loc                    : loc;
        }

and resource_spec = { rs_resources : resource list;
                      rs_loc       : loc;
                    }

and resource = { r_desc : resource_desc;
                 r_loc  : loc;
               }

and resource_desc =
  | RlocalVarDecl of local_variable_declaration
  | RfieldAccess of field_access
  | Rname of name


let set_name_attribute ?(force=false) a n =
  match n.n_desc with
  | Nsimple(at, _) when force -> at := a
  | Nqualified(at, _, _, _) when force -> at := a
  | Nsimple(at, _) -> set1 at a
  | Nqualified(at, _, _, _) -> set1 at a
  | _ -> ()

let set_attribute lattr attr name =
  let(* rec*) set_attr a n =
    match n.n_desc with
    | Nsimple(at, _) -> set1 at a
    | Nqualified(at, (*n*)_, _, _) -> set1 at a;(* set_attr a n*)
    | _ -> ()
  in
  match name.n_desc with
  | Nsimple _ -> set_attr attr name
  | Nqualified(at, n, _, _) -> set_attr lattr n; set1 at attr
  | _ -> ()

let set_attribute_PT_T rr = set_attribute NApackageOrType (NAtype rr)
let set_attribute_P_T rr  = set_attribute NApackage (NAtype rr)
let set_attribute_PT_PT   = set_attribute NApackageOrType NApackageOrType
let set_attribute_P_P     = set_attribute NApackage NApackage
(*let set_attribute_A_M rr  = set_attribute (NAambiguous rr) NAmethod*)
(*let set_attribute_A_E rr  = set_attribute (NAambiguous rr) NAexpression*)


let get_name_attribute name =
  match name.n_desc with
  | Nsimple(attr, _)
  | Nqualified(attr, _, _, _) -> !attr
  | _ -> NAunknown

let compose_name ?(attr=ref NAunknown) name ident =
  let desc = Nqualified(attr, name, [], ident) in
  let loc = Loc.widen name.n_loc ((String.length ident) + 1) in
  {n_desc=desc;n_loc=loc}

let decompose_name name =
  match name.n_desc with
  | Nsimple _ -> failwith "Ast.decompose_name"
  | Nqualified(_, n, _, id) -> n, id
  | _ -> failwith "Ast.decompose_name"

let rec iter_id f n =
  match n.n_desc with
  | Nsimple(_, id) -> f id
  | Nqualified(_, n0, _, id) -> f id; iter_id f n0
  | _ -> ()

let rec leftmost_of_name n =
  match n.n_desc with
  | Nsimple(attr, id) -> attr, id
  | Nqualified(_, n, _, _) -> leftmost_of_name n
  | _ -> ref NAunknown, "?"

let leftmost_identifier n =
  let _, id = leftmost_of_name n in
  id

let rec leftmost_name n =
  match n.n_desc with
  | Nsimple(_, _) -> n
  | Nqualified(_, n, _, _) -> leftmost_name n
  | _ -> n

let is_leftmost_id_capitalized n =
  let id = leftmost_identifier n in
  is_capitalized id

let rightmost_identifier n =
  match n.n_desc with
  | Nsimple(_, id) -> id
  | Nqualified(_, _, _, id) -> id
  | _ -> "?"

let is_rightmost_id_capitalized n =
  match n.n_desc with
  | Nsimple(_, id) -> is_capitalized id
  | Nqualified(_, _, _, id) -> is_capitalized id
  | _ -> false

let is_rightmost_id_all_capitalized n =
  match n.n_desc with
  | Nsimple(_, id) -> is_all_capitalized id
  | Nqualified(_, _, _, id) -> is_all_capitalized id
  | _ -> false

let rightmost_name n =
  match n.n_desc with
  | Nqualified(a, _, _, id) -> {n_desc=Nsimple(a, id);n_loc=n.n_loc}
  | _ -> n

let get_qualifier name =
  match name.n_desc with
  | Nsimple _ -> raise Not_found
  | Nqualified(_, n, _, _) -> n
  | _ -> raise Not_found

let is_rightmost_qualifier_capitalized n =
  try
    let q = get_qualifier n in
    match q.n_desc with
    | Nsimple(_, id)
    | Nqualified(_, _, _, id) -> is_capitalized id
    | _ -> false
  with
  | _ -> false

let qualifier_contains_capitalized n =
  try
    let q = get_qualifier n in
    iter_id
      (fun i ->
        if is_capitalized i then
          raise Exit
      ) q;
    false
  with
  | Exit -> true
  | _ -> false

let is_all_qualifier_lowercase n =
  try
    let q = get_qualifier n in
    iter_id
      (fun i ->
        if is_capitalized i then
          raise Exit
      ) q;
    true
  with
  | _ -> false

let rec get_length name =
  match name.n_desc with
  | Nsimple _ -> 1
  | Nqualified(_, n, _, _) -> 1 + get_length n
  | _ -> raise Not_found

let is_simple n =
  match n.n_desc with
  | Nsimple _ -> true
  | _ -> false

let is_qualified n =
  match n.n_desc with
  | Nqualified _ -> true
  | _ -> false

let is_ambiguous_name name =
  match get_name_attribute name with
  | NAambiguous _ -> true
  | _ -> false

let is_type_name name =
  match get_name_attribute name with
  | NAtype _ -> true
  | NApackageOrType -> true
  | _ -> false

let is_type name =
  match get_name_attribute name with
  | NAtype _ -> true
  | _ -> false

let is_static name =
  match get_name_attribute name with
  | NAstatic _ -> true
  | _ -> false

let is_package_or_type_name name =
  match get_name_attribute name with
  | NApackageOrType -> true
  | _ -> false

let is_expression name =
  match get_name_attribute name with
  | NAexpression _ -> true
  | _ -> false

let is_unknown_expression name =
  match get_name_attribute name with
  | NAexpression EKunknown -> true
  | _ -> false

let is_unknown_name name =
  (get_name_attribute name) = NAunknown

let dummy_name = { n_desc=Nsimple(ref NAunknown, ""); n_loc=Loc.dummy; }


type package_declaration = { pd_annotations : annotations;
			     pd_name        : name;
			     pd_loc         : loc;
			   }

type import_declaration = { id_desc : import_declaration_desc; id_loc : loc; }
and import_declaration_desc =
  | IDsingle of name (* of type *)
  | IDtypeOnDemand of name (* of package or type *)
  | IDsingleStatic of name (* of type *) * identifier
  | IDstaticOnDemand of name (* of package or type *)
  | IDerror of string

type type_declaration = { td_desc : type_declaration_desc; td_loc : loc; }
and type_declaration_desc =
  | TDclass of class_declaration
  | TDinterface of interface_declaration
  | TDempty
  | TDerror of string
  | TDorphan of class_body_declaration

type compilation_unit =
    { cu_package   : package_declaration option;
      cu_imports   : import_declaration list;
      cu_tydecls   : type_declaration list;
      cu_modecl    : module_declaration option;
    }

let _mkprim loc d = { p_desc=d; p_loc=loc }

let mh_is_generic mh = mh.mh_type_parameters <> None

let get_modifiers_from_mh mh =
  match mh.mh_modifiers with
  | Some ms -> ms.ms_modifiers
  | _ -> []

let get_annot_dims_from_type ty =
  match ty.ty_desc with
  | Tarray(_, dl) -> dl
  | _ -> []

let annot_exists =
  List.exists (fun adim -> adim.ad_annotations <> [])

let proc_op proc f op =
  match op with
  | Some x -> proc f x
  | None -> ()

[%%capture_path
let rec proc_element_value f ev =
  match ev.ev_desc with
  | EVconditional e -> proc_expression f e
  | EVannotation a -> proc_annotation f a
  | EVarrayInit evs -> List.iter (proc_element_value f) evs

and proc_annotation f a =
  match a.a_desc with
  | Anormal(n, evps) ->
      f n;
      List.iter (fun evp -> let _, ev = evp.evp_desc in proc_element_value f ev) evps
  | Amarker n -> f n
  | AsingleElement(n, ev) ->
      f n;
      proc_element_value f ev

and proc_type f ty =
  match ty.ty_desc with
  | TclassOrInterface tss
  | Tclass tss
  | Tinterface tss -> List.iter (proc_type_spec f) tss
  | Tarray(ty0, _) -> proc_type f ty0
  | _ -> ()

and proc_type_spec f ts =
  match ts with
  | TSname(al, n) -> List.iter (proc_annotation f) al; f n
  | TSapply(al, n, tas) ->
      List.iter (proc_annotation f) al;
      f n;
      proc_type_arguments f tas

and proc_expression f e =
  match e.e_desc with
  | Eprimary p -> proc_primary f p
  | Eunary(_, e0) -> proc_expression f e0
  | Ebinary(_, e0, e1) -> List.iter (proc_expression f) [e0; e1]
  | Ecast(ty, e0) -> proc_type f ty; proc_expression f e0
  | Einstanceof(e0, ty) -> proc_expression f e0; proc_type f ty
  | EinstanceofP(e0, lvd) -> proc_expression f e0; proc_local_variable_declaration f lvd
  | Econd(e0, e1, e2) -> List.iter (proc_expression f) [e0; e1; e2]
  | Eassignment(lhs, _, rhs) -> List.iter (proc_expression f) [lhs; rhs]
  | Elambda(_, b) -> proc_lambda_block f b
  | Eswitch(e, swb) -> begin
      proc_expression f e;
      List.iter
        (fun (sls, bss) ->
          List.iter (proc_switch_label f) sls;
          List.iter (proc_block_statement f) bss)
        swb.sb_switch_block_stmt_grps
  end
  | _ -> ()

and proc_lambda_block f = function
  | LBexpr e -> proc_expression f e
  | LBblock b -> proc_block f b

and _name_to_facc name =
  match name.n_desc with
  | Nsimple(a, _) -> begin
      match !a with
      | NAexpression (EKfacc|EKunknown) -> PfieldAccess(FAimplicit name)
      | NAexpression EKname -> Pname name
      | _ -> Pname name
  end
  | Nqualified(_, n, [], i) -> PfieldAccess(FAprimary(name_to_facc n, i))
  | Nqualified(_, _, _, _) -> Pname name
  | Nerror _ -> Pname name

and name_to_facc name = _mkprim name.n_loc (_name_to_facc name)

and proc_primary f p =
  [%debug_log "[%s] %s" (Loc.to_string p.p_loc) (prim_to_string p)];
  match p.p_desc with
  | Pname n -> begin
      f n;
      [%debug_log "[%s] %s" (Loc.to_string p.p_loc) (prim_to_string p)];
      if is_qualified n then begin
        let q = get_qualifier n in
        if is_expression q then begin
          p.p_desc <- _name_to_facc n;
          [%debug_log "[%s] -> %s" (Loc.to_string p.p_loc) (prim_to_string p)]
        end
      end
  end
  | PclassLiteral ty -> proc_type f ty
  | PqualifiedThis n -> f n
  | Pparen e -> proc_expression f e
  | PclassInstanceCreation cic -> proc_class_instance_creation f cic
  | PfieldAccess (FAimplicit n) when is_type_name n -> begin
      f n;
      [%debug_log "[%s] %s" (Loc.to_string p.p_loc) (prim_to_string p)];
      p.p_desc <- Pname n;
      [%debug_log "[%s] -> %s" (Loc.to_string p.p_loc) (prim_to_string p)]
  end
  | PfieldAccess (FAimplicit n) when is_ambiguous_name n -> begin
      f n;
      [%debug_log "[%s] %s" (Loc.to_string p.p_loc) (prim_to_string p)];
      if is_type_name n || is_static n then begin
        p.p_desc <- Pname n;
        [%debug_log "[%s] -> %s" (Loc.to_string p.p_loc) (prim_to_string p)]
      end
  end
  | PfieldAccess fa -> proc_field_access f fa
  | PmethodInvocation mi -> proc_method_invocation f mi
  | ParrayAccess aa -> proc_array_access f aa
  | ParrayCreationExpression ace -> proc_array_creation_expression f ace
  | PmethodReference mr -> proc_method_reference f mr
  | _ -> ()

and proc_class_instance_creation f cic =
  match cic.cic_desc with
  | CICunqualified(tas_op, ty, args, cb_op) ->
      proc_op proc_type_arguments f tas_op;
      proc_type f ty;
      proc_arguments f args;
      proc_op proc_class_body f cb_op
  | CICqualified(p, tas0_op, _, tas1_op, args, cb_op) ->
      proc_primary f p;
      proc_op proc_type_arguments f tas0_op;
      proc_op proc_type_arguments f tas1_op;
      proc_arguments f args;
      proc_op proc_class_body f cb_op
  | CICnameQualified(n, tas0_op, _, tas1_op, args, cb_op) ->
      f n;
      proc_op proc_type_arguments f tas0_op;
      proc_op proc_type_arguments f tas1_op;
      proc_arguments f args;
      proc_op proc_class_body f cb_op

and proc_class_body_declaration f cbd =
  match cbd.cbd_desc with
  | CBDfield fd -> proc_field_declaration f fd
  | CBDmethod(mh, b_op) ->
      proc_method_header f mh;
      proc_op proc_block f b_op
  | CBDclass cd -> proc_class_declaration f cd
  | CBDinterface id -> proc_interface_declaration f id
  | CBDstaticInitializer b -> proc_block f b
  | CBDinstanceInitializer b -> proc_block f b
  | CBDconstructor cd -> proc_constructor_declaration f cd
  | _ -> ()

and proc_record_body_declaration f rbd =
  match rbd.rbd_desc with
  | RBDclass_body_decl c -> proc_class_body_declaration f c
  | RBDcompact_ctor_decl c -> proc_compact_ctor_decl f c

and proc_compact_ctor_decl f ccnd =
  proc_op proc_modifiers f ccnd.ccnd_modifiers;
  proc_constructor_body f ccnd.ccnd_body

and proc_type_bound f tb =
  proc_type f tb.tb_reference_type;
  List.iter (fun ab -> proc_type f ab.ab_interface) tb.tb_additional_bounds

and proc_type_parameter f tp =
  proc_op proc_type_bound f tp.tp_type_bound

and proc_type_parameters f tps =
  List.iter (proc_type_parameter f) tps.tps_type_parameters

and proc_method_header f mh =
  proc_op proc_modifiers f mh.mh_modifiers;
  proc_op proc_type_parameters f mh.mh_type_parameters;
  List.iter (proc_annotation f) mh.mh_annotations;
  proc_type f mh.mh_return_type;
  List.iter (proc_formal_parameter f) mh.mh_parameters;
  proc_op proc_throws f mh.mh_throws

and proc_formal_parameter f fp =
  proc_op proc_modifiers f fp.fp_modifiers;
  proc_type f fp.fp_type

and proc_throws f th =
  List.iter (proc_type f) th.th_exceptions

and proc_array_initializer f ai =
  List.iter (proc_variable_initializer f) ai

and proc_variable_initializer f vi =
  match vi.vi_desc with
  | VIexpression e -> proc_expression f e
  | VIarray ai -> proc_array_initializer f ai
  | VIerror _ -> ()

and proc_variable_declarator f vd =
  proc_op proc_variable_initializer f vd.vd_variable_initializer

and proc_local_variable_declaration f lvd =
  proc_op proc_modifiers f lvd.lvd_modifiers;
  proc_type f lvd.lvd_type;
  List.iter (proc_variable_declarator f) lvd.lvd_variable_declarators

and proc_statement_expression f se =
  match se.se_desc with
  | SEassignment(lhs, _, rhs) -> List.iter (proc_expression f) [lhs; rhs]
  | SEpreIncrement e
  | SEpreDecrement e
  | SEpostIncrement e
  | SEpostDecrement e -> proc_expression f e
  | SEmethodInvocation mi -> proc_method_invocation f mi
  | SEclassInstanceCreation cic -> proc_class_instance_creation f cic
  | _ -> ()

and proc_switch_label f sl =
  match sl.sl_desc with
  | SLconstant el -> List.iter (proc_expression f) el
  | SLdefault -> ()

and proc_statement f s =
  match s.s_desc with
  | Sblock b -> proc_block f b
  | Sexpression se -> proc_statement_expression f se
  | Sswitch(e, swb) ->
      proc_expression f e;
      List.iter
        (fun (sls, bss) ->
          List.iter (proc_switch_label f) sls;
          List.iter (proc_block_statement f) bss)
        swb.sb_switch_block_stmt_grps
  | Sdo(s0, e) ->
      proc_statement f s0;
      proc_expression f e
  | Sreturn e_op -> proc_op proc_expression f e_op
  | Ssynchronized(e, b) ->
      proc_expression f e;
      proc_block f b
  | Stry(rs_op, b, cts_op, fin_op) ->
      proc_op proc_resource_spec f rs_op;
      proc_block f b;
      proc_op (fun f catches -> List.iter (proc_catch f) catches) f cts_op;
      proc_op (fun f fin -> proc_block f fin.f_block) f fin_op
  | Syield e ->
      proc_expression f e
  | Slabeled(_, s0) -> proc_statement f s0
  | SifThen(e, s0)
  | Swhile(e, s0) ->
      proc_expression f e;
      proc_statement f s0
  | SifThenElse(e, s0, s1) ->
      proc_expression f e;
      List.iter (proc_statement f) [s0; s1]
  | Sfor(fi_op, e_op, ses, s0) ->
      proc_op proc_for_init f fi_op;
      proc_op proc_expression f e_op;
      List.iter (proc_statement_expression f) ses;
      proc_statement f s0
  | SforEnhanced(fp, e, s0) ->
      proc_formal_parameter f fp;
      proc_expression f e;
      proc_statement f s0
  | Sthrow e
  | Sassert1 e -> proc_expression f e
  | Sassert2(e0, e1) -> List.iter (proc_expression f) [e0; e1]
  | _ -> ()

and proc_resource_spec f rs = List.iter (proc_resource f) rs.rs_resources

and proc_resource f r =
  match r.r_desc with
  | RlocalVarDecl lvd -> proc_local_variable_declaration f lvd
  | RfieldAccess fa -> proc_field_access f fa
  | Rname n -> f n

and proc_catch f c =
  proc_catch_formal_parameter f c.c_formal_parameter;
  proc_block f c.c_block

and proc_catch_formal_parameter f cfp =
  proc_op proc_modifiers f cfp.cfp_modifiers;
  List.iter (proc_type f) cfp.cfp_type_list

and proc_for_init f fi =
  match fi.fi_desc with
  | FIstatement ses -> List.iter (proc_statement_expression f) ses
  | FIlocal lvd -> proc_local_variable_declaration f lvd

and proc_block_statement f bs =
  match bs.bs_desc with
  | BSlocal lvd -> proc_local_variable_declaration f lvd
  | BSclass cd -> proc_class_declaration f cd
  | BSstatement s -> proc_statement f s
  | _ -> ()

and proc_block f b =
  List.iter (proc_block_statement f) b.b_block_statements

and proc_extends_class f exc =
  proc_type f exc.exc_class

and proc_implements f im =
  List.iter (proc_type f) im.im_interfaces

and proc_permits f pm =
  List.iter f pm.pm_type_names

and proc_class_declaration_head f ch =
  proc_op proc_modifiers f ch.ch_modifiers;
  proc_op proc_type_parameters f ch.ch_type_parameters;
  proc_op proc_extends_class f ch.ch_extends_class;
  proc_op proc_implements f ch.ch_implements;
  proc_op proc_permits f ch.ch_permits

and proc_record_declaration_head f rh =
  proc_op proc_modifiers f rh.rh_modifiers;
  proc_op proc_type_parameters f rh.rh_type_parameters;
  List.iter (proc_formal_parameter f) rh.rh_record_header;
  proc_op proc_implements f rh.rh_implements

and proc_class_declaration f cd =
  match cd.cd_desc with
  | CDclass(ch, cb) ->
      proc_class_declaration_head f ch;
      proc_class_body f cb
  | CDenum(eh, eb) ->
      proc_class_declaration_head f eh;
      proc_enum_body f eb
  | CDrecord(rh, cb) ->
      proc_record_declaration_head f rh;
      proc_record_body f cb
  | CDaspect(ah, ab) ->
      proc_class_declaration_head f ah;
      proc_aspect_body f ab

and proc_aspect_body f ab =
  List.iter (proc_class_body_declaration f) ab.abd_aspect_body_declarations

and proc_enum_body f eb =
  List.iter (proc_enum_constant f) eb.eb_enum_constants;
  List.iter (proc_class_body_declaration f) eb.eb_class_body_declarations

and proc_enum_constant f ec =
  List.iter (proc_annotation f) ec.ec_annotations;
  proc_op proc_arguments f ec.ec_arguments;
  proc_op proc_class_body f ec.ec_class_body

and proc_interface_declaration_head f ifh =
  proc_op proc_modifiers f ifh.ifh_modifiers;
  proc_op proc_type_parameters f ifh.ifh_type_parameters;
  proc_op (fun f ei -> List.iter (proc_type f) ei.exi_interfaces) f ifh.ifh_extends_interfaces;
  proc_op proc_permits f ifh.ifh_permits

and proc_interface_declaration f ifd =
  match ifd.ifd_desc with
  | IFDnormal(ih, ib) ->
      proc_interface_declaration_head f ih;
      proc_interface_body f ib
  | IFDannotation(_, atb) ->
      List.iter (proc_annotation_type_member_declaration f) atb.atb_member_declarations

and proc_annotation_type_member_declaration f atmd =
  match atmd.atmd_desc with
  | ATMDconstant fd -> proc_field_declaration f fd
  | ATMDelement(_, ty, _, dl, dv_op) ->
      proc_type f ty;
      List.iter (fun d -> List.iter (proc_annotation f) d.ad_annotations) dl;
      proc_op proc_element_value f dv_op
  | ATMDclass cd -> proc_class_declaration f cd
  | ATMDinterface id -> proc_interface_declaration f id
  | _ -> ()

and proc_interface_body f ib =
  List.iter (proc_interface_member_declaration f) ib.ib_member_declarations

and proc_interface_member_declaration f imd =
  match imd.imd_desc with
  | IMDconstant fd         -> proc_field_declaration f fd
  | IMDinterfaceMethod amd -> proc_interface_method_declaration f amd
  | IMDclass cd            -> proc_class_declaration f cd
  | IMDinterface ifd       -> proc_interface_declaration f ifd
  | _ -> ()

and proc_modifiers f ms =
  List.iter (proc_modifier f) ms.ms_modifiers

and proc_modifier f m =
  match m.m_desc with
  | Mannotation a -> proc_annotation f a
  | _ -> ()

and proc_field_declaration f fd =
  proc_op proc_modifiers f fd.fd_modifiers;
  proc_type f fd.fd_type;
  List.iter (proc_variable_declarator f) fd.fd_variable_declarators

and proc_interface_method_declaration f amd =
  proc_method_header f amd.amd_method_header;
  proc_op proc_block f amd.amd_body

and proc_constructor_declaration f cnd =
  proc_op proc_modifiers f cnd.cnd_modifiers;
  proc_op proc_type_parameters f cnd.cnd_type_parameters;
  List.iter (proc_formal_parameter f) cnd.cnd_parameters;
  proc_op proc_throws f cnd.cnd_throws;
  proc_constructor_body f cnd.cnd_body

and proc_constructor_body f cnb =
  proc_op proc_explicit_constructor_invocation f cnb.cnb_explicit_constructor_invocation;
  List.iter (proc_block_statement f) cnb.cnb_block

and proc_explicit_constructor_invocation f eci =
  match eci.eci_desc with
  | ECIthis(tas_op, args)
  | ECIsuper(tas_op, args) ->
      proc_op proc_type_arguments f tas_op;
      proc_arguments f args
  | ECIprimary(p, tas_op, args) ->
      proc_primary f p;
      proc_op proc_type_arguments f tas_op;
      proc_arguments f args
  | ECIname(n, tas_op, args) ->
      f n;
      proc_op proc_type_arguments f tas_op;
      proc_arguments f args
  | _ -> ()

and proc_method_reference f mr =
  match mr.mr_desc with
  | MRname(n, tas_opt, _)
  | MRtypeSuper(n, tas_opt, _) ->
      f n;
      proc_op proc_type_arguments f tas_opt

  | MRtypeNew(ty, tas_opt) ->
      proc_type f ty;
      proc_op proc_type_arguments f tas_opt

  | MRprimary(p, tas_opt, _) ->
      proc_primary f p;
      proc_op proc_type_arguments f tas_opt

  | MRsuper(tas_opt, _) ->
      proc_op proc_type_arguments f tas_opt

and proc_class_body f cb =
  List.iter (proc_class_body_declaration f) cb.cb_class_body_declarations

and proc_record_body f rb =
  List.iter (proc_record_body_declaration f) rb.rb_record_body_declarations

and proc_arguments f args =
  List.iter (proc_expression f) args.as_arguments

and proc_type_argument f ta =
  match ta.ta_desc with
  | TAreferenceType ty -> proc_type f ty
  | TAwildcard wc -> proc_wildcard f wc

and proc_wildcard f (al, wb) =
  List.iter (proc_annotation f) al;
  proc_op proc_wildcard_bounds f wb

and proc_wildcard_bounds f wb =
  match wb.wb_desc with
  | WBextends ty
  | WBsuper ty -> proc_type f ty

and proc_type_arguments f targs =
  List.iter (proc_type_argument f) targs.tas_type_arguments

and proc_field_access f fa =
  match fa with
  | FAprimary(p, _) -> proc_primary f p
  | FAclassSuper(n, _) -> f n
  | _ -> ()

and name_attribute_to_string = function
  | NApackage       -> "P"
  | NAtype _        -> "T"
  | NAexpression EKfacc -> "Ef"
  | NAexpression EKname -> "En"
  | NAexpression EKunknown -> "E"
  | NAmethod        -> "M"
  | NApackageOrType -> "PT"
  | NAstatic _      -> "S"
  | NAambiguous _   -> "A"
  | NAunknown       -> "U"

and name_to_simple_string name =
  match name.n_desc with
  | Nsimple(_, sn) -> sn
  | Nqualified(_, n, _, sn) ->
      sprintf "%s.%s" (name_to_simple_string n) sn
  | Nerror s -> s

and name_to_string name =
  match name.n_desc with
  | Nsimple(attr, sn) ->
      sprintf "(%s)_%s" sn (name_attribute_to_string !attr)

  | Nqualified(attr, n, _, sn) ->
      sprintf "(%s.%s)_%s" (name_to_string n) sn (name_attribute_to_string !attr)

  | Nerror s -> s

and prim_to_string p =
  match p.p_desc with
  | Pname n -> sprintf "Pname:%s" (name_to_string n)
  | PfieldAccess (FAimplicit n) -> sprintf "PfieldAccess:FAimplicit:%s" (name_to_string n)
  | PfieldAccess (FAprimary(p, id)) ->
      sprintf "PfieldAccess:FAprimary:(%s):%s" (prim_to_string p) id
  | PfieldAccess _ -> "PfieldAcess"
  | PqualifiedThis n -> sprintf "PqualifiedThis:%s" (name_to_string n)
  | Pliteral _ -> "Pliteral"
  | PclassLiteral _ -> "PclassLiteral"
  | PclassLiteralVoid -> "PclassLiteralVoid"
  | Pthis -> "Pthis"
  | Pparen _ -> "Pparen"
  | PclassInstanceCreation _ -> "PclassInstanceCreation"
  | PmethodInvocation _ -> "PmethodInvocation"
  | ParrayAccess _ -> "ParrayAccess"
  | ParrayCreationExpression _ -> "ParrayCreationExpression"
  | PmethodReference _ -> "PmethodReference"
  | Perror err -> err

and proc_method_invocation f mi =
  let proc = function
    | MImethodName(n, args) ->
        f n;
        proc_arguments f args
    | MIprimary(p, tas_op, id, args) -> begin
        [%debug_log "[%s] %s %s" (Loc.to_string mi.mi_loc) (prim_to_string p) id];
        proc_primary f p;
        proc_op proc_type_arguments f tas_op;
        proc_arguments f args;
        [%debug_log "[%s] %s %s" (Loc.to_string mi.mi_loc) (prim_to_string p) id];
        match p.p_desc with
        | Pname n | PfieldAccess (FAimplicit n) when is_type_name n ->
            mi.mi_desc <- MItypeName(n, tas_op, id, args)
        | _ -> ()
    end
    | MIsuper(_, tas_op, _, args) ->
        proc_op proc_type_arguments f tas_op;
        proc_arguments f args
    | MItypeName(n, tas_op, _, args)
    | MIclassSuper(_, _, n, tas_op, _, args) ->
        f n;
        proc_op proc_type_arguments f tas_op;
        proc_arguments f args
  in
  proc mi.mi_desc

and proc_array_access f aa =
  match aa.aa_desc with
  | AAname(n, e) ->
      f n;
      proc_expression f e
  | AAprimary(p, e) ->
      proc_primary f p;
      proc_expression f e

and proc_array_creation_expression f ace =
  match ace with
  | ACEtype(ty, des, _) ->
      proc_type f ty;
      List.iter (fun de -> proc_expression f de.de_desc) des
  | ACEtypeInit(ty, _, ai) ->
      proc_type f ty;
      proc_array_initializer f ai

and proc_type_declaration f td =
  match td.td_desc with
  | TDclass cd -> proc_class_declaration f cd
  | TDinterface id -> proc_interface_declaration f id
  | _ -> ()
]

let proc_import_declaration f id =
  match id.id_desc with
  | IDsingle n
  | IDtypeOnDemand n
  | IDsingleStatic(n, _)
  | IDstaticOnDemand n -> f n
  | IDerror _ -> ()

class c (compilation_unit : compilation_unit) = object(* (self)*)
  inherit Ast_base.c

  val mutable nintegers = -1
  val mutable nfloats   = -1
  val mutable nstrings  = -1

  method set_nintegers x = nintegers <- x
  method set_nfloats x = nfloats <- x
  method set_nstrings x = nstrings <- x

  method nintegers = nintegers
  method nfloats = nfloats
  method nstrings = nstrings

  method compilation_unit = compilation_unit

  method iter_name f =
    begin
      match compilation_unit.cu_package with
      | Some pdecl ->
	  List.iter (proc_annotation f) pdecl.pd_annotations;
	  f pdecl.pd_name
      | None -> ()
    end;
    List.iter (proc_import_declaration f) compilation_unit.cu_imports;
    List.iter (proc_type_declaration f) compilation_unit.cu_tydecls

end (* of class Ast.c *)

let dummy_type = { ty_desc=Tvoid; ty_loc=Loc.dummy; }

type declaration =
    | D_import of import_declaration
    | D_type of type_declaration

let partition_declarations dl =
  let il_, tl_ =
    List.partition
      (function
        | D_import _ -> true
        | _ -> false
      ) dl
  in
  let il =
    List.map
      (function
        | D_import i -> i
        | _ -> assert false
      ) il_
  in
  let tl =
    List.map
      (function
        | D_type t -> t
        | _ -> assert false
      ) tl_
  in
  il, tl


(* end of Ast *)
