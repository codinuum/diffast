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

(* Labels *)

module AccessSpec            = F_access_spec
module Ambiguous             = F_ambiguous
module AttrSpec              = F_attr_spec
module CaseSelector          = F_case_selector
module CaseValueRange        = F_case_value_range
module CloseSpec             = F_close_spec
module ConnectSpec           = F_connect_spec
module Constant              = F_constant
module ControlEditDesc       = F_control_edit_desc
module DefinedOperator       = F_defined_operator
module Format                = F_format
module FormatItem            = F_format_item
module GenericSpec           = F_generic_spec
module InquireSpec           = F_inquire_spec
module IntentSpec            = F_intent_spec
module InternalSubprogram    = F_internal_subprogram
module IntrinsicOperator     = F_intrinsic_operator
module IoControlSpec         = F_io_control_spec
module LindaCall             = F_linda_call
module ModuleSubprogram      = F_module_subprogram
module OclDirective          = F_ocl_directive
module OmpClause             = F_omp_clause
module OmpDirective          = F_omp_directive
module OmpConstruct          = F_omp_construct
module AccClause             = F_acc_clause
module AccDirective          = F_acc_directive
module AccConstruct          = F_acc_construct
module DecClause             = F_dec.Clause
module DecDirective          = F_dec.Directive
module PositionSpec          = F_position_spec
module PpDirective           = F_pp_directive
module PrefixSpec            = F_prefix_spec
module ProgramUnit           = F_program_unit
module Stmt                  = F_stmt
module TypeAttrSpec          = F_type_attr_spec
module TypeSpec              = F_type_spec
module Xlf                   = F_xlf
module Dec                   = F_dec
module BindingAttr           = F_binding_attr
module ProcComponentAttrSpec = F_proc_component_attr_spec
module ProcAttrSpec          = F_proc_attr_spec
module WaitSpec              = F_wait_spec
module FlushSpec             = F_flush_spec
module HeaderFile            = F_header_file
