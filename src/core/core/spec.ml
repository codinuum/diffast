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
(* *)

module Xset = Diffast_misc.Xset
module Compression = Diffast_misc.Compression
module Otree = Diffast_misc.Otree
module UID = Diffast_misc.UID
module GI = Diffast_misc.GIndex
module Path = Diffast_misc.Path
module Storage = Diffast_misc.Storage
module Binding = Diffast_misc.Binding
module Loc = Diffast_misc.Loc

module SB = Spec_base



class type node_data_t = object ('self)
  inherit SB.node_data_t_shared

  method set_prefix : string -> unit
  method get_prefix : string

  method set_suffix : string -> unit
  method get_suffix : string

  method gid     : GI.t
  method set_gid : GI.t -> unit

  method frommacro     : string
  method is_frommacro  : bool
  method not_frommacro : bool
  method set_frommacro : string -> unit

  method _annotation     : Obj.t

  method is_sequence     : bool
  method is_ntuple       : bool
  method is_phantom      : bool
  method is_special      : bool

  method stripped_label    : string

  method anonymized_label  : string
  method more_anonymized_label : string
  method anonymized2_label : string
  method anonymized3_label : string

  method to_simple_string  : string

  method is_anonymous_orig : bool

  method get_category : string
  method get_value    : string
  method has_value    : bool
  method has_non_trivial_value : bool
  method has_non_trivial_tid : bool
  method is_string_literal : bool
  method is_int_literal    : bool
  method is_real_literal   : bool
  method is_literal        : bool
  method is_statement      : bool
  method is_block          : bool
  method is_primary        : bool
  method is_op             : bool

  method is_scope_creating : bool

  method move_disallowed : bool
  method is_common       : bool

  method is_order_insensitive : bool

  method get_ident_use : string

  method orig_lab_opt  : Obj.t option

  method binding : Binding.t
  method set_binding : Binding.t -> unit
  method set_bindings : Binding.t list -> unit
  method add_binding : Binding.t -> unit

  method scope_node : 'self Otree.node2
  method set_scope_node : 'self Otree.node2 -> unit

  method successors    : ('self Otree.node2) Xset.t
  method add_successor : ('self Otree.node2) -> unit

  method has_ordinal : bool
  method get_ordinal : int -> int
  method add_to_ordinal_list : int list -> unit

  method id_loc : Loc.t

  (* for searchast *)
  method char              : char
  method to_short_string   : string

end (* of class type node_data_t *)


type node_t = node_data_t SB.node_t




class type tree_t = object ('self)
  inherit [ node_t ] SB.tree_t_shared

  method unparse_subtree_ch       : ?no_boxing:bool -> ?no_header:bool -> ?fail_on_error:bool -> node_t -> SB.OutChannel.t -> unit
  method unparse_ch               : ?no_boxing:bool -> ?no_header:bool -> ?fail_on_error:bool -> SB.OutChannel.t -> unit

  method set_true_parent_tbl      : (UID.t, node_t) Hashtbl.t -> unit
  method find_true_parent         : UID.t -> node_t

  method set_true_children_tbl    : (node_t, node_t array) Hashtbl.t -> unit
  method recover_true_children    : initial_only:bool -> unit -> unit
  method has_true_children        : node_t -> bool

  method set_source_info          : Storage.file -> unit

  method set_source_fullpath      : string -> unit
  method source_fullpath          : string
  method source_kind              : Storage.kind
  method set_source_kind          : Storage.kind -> unit
  method set_vkind                : Entity.vkind -> unit
  method vkind                    : Entity.vkind
  method set_version              : string -> unit
  method version                  : string
  method set_proj_root            : string -> unit
  method proj_root                : string
  method set_source_digest        : string -> unit
  method source_digest            : string
  method encoded_source_digest    : string
  method set_parser_name          : string -> unit

  method dump_astml               : ?comp:Compression.c -> string -> unit

(*
  method set_line_terminator      : string -> unit
  method line_terminator          : string
  method line_terminator_name     : string
*)

  method collapse                 : unit

  method dump_line_ranges         : string -> unit



  method set_misparsed_regions    : (int * int) list -> unit
  method misparsed_regions        : (int * int) list
  method set_total_LOC            : int -> unit
  method total_LOC                : int
  method set_misparsed_LOC        : int -> unit
  method misparsed_LOC            : int

  method get_nearest_containing_unit      : node_t -> node_t
  method label_match                      : string -> bool

  method align_fragments                  : (GI.t * GI.t) list -> 'self -> unit


  method nearest_common_ancestor          : ?closed:bool -> node_t list -> node_t * int
  method get_nearest_boundary             : node_t -> node_t

  method find_nodes_by_line_range         : (int * int) -> node_t list
  method find_nodes_by_line_col_range     : ((int * int) * (int * int)) -> node_t list

  method get_ident_use_list               : GI.t -> string list

  method merge_locs_adjusting_to_boundary : GI.t list -> Loc.t

  method subtree_to_simple_string         : GI.t -> string

  method make_anonymized_subtree_copy     : ?nds_left_named:(node_t list) -> node_t -> 'self
  method make_anonymized2_subtree_copy    : ?nds_left_named:(node_t list) -> node_t -> 'self
  method make_anonymized3_subtree_copy    : ?nds_left_named:(node_t list) -> node_t -> 'self

  method find_label                       : node_t -> node_t -> node_t list


  (* for searchast *)

  method find_token_node          : int -> node_t
  method find_token_node_pat      : int -> node_t
  method to_token_array           : string array
  method get_token_array_pat      : GIDfragment.c -> string array
  method match_pat_ch             : string -> 'self -> string array -> GIDfragment.c -> out_channel -> unit
  method match_token_array_pat_ch : string -> string -> string -> string array -> out_channel -> unit
  method match_pats               : string -> string -> 'self -> GIDfragment.c list -> unit
  method show_node_array_pat      : unit


end (* of class type tree_t *)





class type nmapping_t = object ('self)

  method use_crossing_or_incompatible_matches_count_cache : bool

  method clear_crossing_or_incompatible_matches_count_cache : unit
  method crossing_or_incompatible_matches_count_cache_hit_count : int
  method size_of_crossing_or_incompatible_matches_count_cache : int

  method clear_starting_pairs_for_glueing : unit
  method set_starting_pairs_for_glueing   : ((node_t * node_t) list) -> unit
  method add_starting_pairs_for_glueing   : ((node_t * node_t) list) -> unit
  method starting_pairs_for_glueing       : ((node_t * node_t) list)


  method is_locked_node     : node_t -> bool
  method lock_node          : ?key:Key.t -> node_t -> unit
  method unlock_node        : node_t -> unit
  method key_of_locked_node : node_t -> Key.t

  method stable_pairs     : (node_t, node_t) Hashtbl.t
  method set_stable_pairs : (node_t, node_t) Hashtbl.t -> unit
  method is_stable_pair   : node_t -> node_t -> bool
  method add_stable_pair  : node_t -> node_t -> unit
  method find_stable_pair : node_t -> node_t list
  method iter_stable_pairs : (node_t -> node_t -> unit) -> unit

  method set_blacklist1 : (node_t, bool) Hashtbl.t -> unit
  method set_blacklist2 : (node_t, bool) Hashtbl.t -> unit

  method size : int

  method iter           : (node_t -> node_t -> unit) -> unit
  method iter_rev       : (node_t -> node_t -> unit) -> unit
  method iter_unsettled : (node_t -> node_t -> unit) -> unit
  method iter_settled   : (node_t -> node_t -> unit) -> unit

  method iter_sorted           : (node_t -> node_t -> int) -> (node_t -> node_t -> unit) -> unit
  method iter_unsettled_sorted : (node_t -> node_t -> int) -> (node_t -> node_t -> unit) -> unit
  method iter_settled_sorted   : (node_t -> node_t -> int) -> (node_t -> node_t -> unit) -> unit


  method find_unsettled : node_t -> node_t
  method find_settled   : node_t -> node_t
  method find           : node_t -> node_t
  method inv_find       : node_t -> node_t

  method add_unsettled     : node_t -> node_t -> unit
  method add_settled       : ?stable:bool -> node_t -> node_t -> unit
  method add_settled_roots    : node_t -> node_t -> unit
  method is_settled_root_pair : node_t -> node_t -> bool

  method iter_settled_roots : (node_t -> node_t -> unit) -> unit
  method iter_settled_roots_sorted : (node_t -> node_t -> int) -> (node_t -> node_t -> unit) -> unit

  method merge_no_override : 'self -> unit
  method merge             : 'self -> unit
  method merge_checked     : 'self -> unit

  method mem           : node_t -> bool
  method mem_unsettled : node_t -> bool
  method mem_settled   : node_t -> bool

  method remove         : node_t -> node_t -> bool
  method remove_settled : node_t -> node_t -> unit

  method filter : (node_t -> node_t -> bool) -> unit

  method promote : node_t -> node_t -> unit
  method demote  : node_t -> node_t -> unit

  method to_list_unsettled : (node_t * node_t) list
  method to_list_settled   : (node_t * node_t) list
  method to_list           : (node_t * node_t) list

  method cod : node_t list
  method dom : node_t list

  method cod_unsettled : node_t list
  method dom_unsettled : node_t list

  method cod_settled : node_t list
  method dom_settled : node_t list

  method has_settled_mapping   : node_t -> node_t -> bool
  method has_unsettled_mapping : node_t -> node_t -> bool
  method has_mapping           : node_t -> node_t -> bool

  method to_string_gid : string
  method to_string     : string

  method dump : string -> unit

  method dump_with_info : ?comp:Compression.c -> string -> unit

  method print_status : unit

  method setup_rev_map : unit

  method mem_dom : node_t -> bool
  method mem_cod : node_t -> bool

  method mem_dom_settled : node_t -> bool
  method mem_cod_settled : node_t -> bool

  method mem_dom_unsettled : node_t -> bool
  method mem_cod_unsettled : node_t -> bool

  method cleanup_ghost : unit

  method count_p_mapping : (node_t -> node_t -> node_t -> node_t -> bool) -> node_t -> node_t -> int
  method count_crossing_mapping                 : node_t -> node_t -> int
  method count_crossing_matches                 : node_t -> node_t -> int
  method count_crossing_or_incompatible_matches : node_t -> node_t -> int
  method count_compatible_noncrossing_matches   : node_t -> node_t -> int

  method iter_p_mapping :
      (node_t -> node_t -> node_t -> node_t -> bool)
    -> node_t -> node_t -> (node_t -> node_t -> unit) -> unit
  method iter_crossing_mapping : node_t -> node_t -> (node_t -> node_t -> unit) -> unit
  method iter_crossing_mapping : node_t -> node_t -> (node_t -> node_t -> unit) -> unit
  method iter_crossing_or_incompatible_mapping :
      node_t -> node_t -> (node_t -> node_t -> unit) -> unit

  method setup_partitions : unit
  method partition_nodes1 : node_t list -> node_t list array
  method partition_nodes2 : node_t list -> node_t list array

  method get_subtree_match_score : node_t -> node_t -> int

end (* of class type nmapping_t *)



module type LABEL_T = sig

  type annotation

  val null_annotation      : annotation
  val annotation_to_string : annotation -> string

  type t

  val lang_prefix : string

  val to_string        : t -> string
  val to_char          : t -> char
  val to_short_string  : ?ignore_identifiers_flag:bool -> t -> string
  val to_simple_string : t -> string

  val to_elem_data     : ?strip:bool -> ?afilt:(string -> bool) -> Loc.t -> t -> string * (string * string) list * string
  val of_elem_data     : string -> (string * string) list -> string -> t

  val relabel_allowed          : t * t -> bool
  val quasi_eq                 : t -> t -> bool
  val is_compatible            : ?weak:bool -> t -> t -> bool
  val is_order_insensitive     : t -> bool
  val move_disallowed          : t -> bool
  val is_common                : t -> bool
  val is_to_be_notified        : t -> bool
  val is_collapse_target       : #Parser_options.c -> t -> bool
  val is_hunk_boundary         : t -> t -> bool
  val forced_to_be_collapsible : t -> bool
  val is_named                 : t -> bool
  val is_named_orig            : t -> bool
  val keyroot_depth_min        : int

  val is_boundary        : t -> bool
  val is_partition       : t -> bool
  val is_sequence        : t -> bool
  val is_ntuple          : t -> bool

  val strip              : t -> t

  val anonymize          : ?more:bool -> t -> t
  val anonymize2         : t -> t
  val anonymize3         : t -> t
  val get_ident_use      : t -> string

  val get_category       : t -> string
  val get_name           : ?strip:bool -> t -> string
  val get_value          : t -> string
  val has_value          : t -> bool
  val has_non_trivial_value : t -> bool
  val has_non_trivial_tid   : t -> bool
  val cannot_be_keyroot  : node_t -> bool

  val is_phantom         : t -> bool
  val is_special         : t -> bool

  val is_string_literal  : t -> bool
  val is_int_literal     : t -> bool
  val is_real_literal    : t -> bool

  val is_statement       : t -> bool
  val is_block           : t -> bool
  val is_primary         : t -> bool
  val is_op              : t -> bool

  val is_scope_creating : t -> bool

  val to_tag             : ?strip:bool -> t -> string * (string * string) list

end (* of module type LABEL_T *)


class type npairs_t = object ('self)

  method mem : node_t -> node_t -> bool
  method add : node_t -> node_t -> unit
  method iter : (node_t -> node_t -> unit) -> unit

end
