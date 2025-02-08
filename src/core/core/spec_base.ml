(*
   Copyright 2012-2024 Codinuum Software Lab <https://codinuum.com>

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

module Xchannel = Diffast_misc.Xchannel
module Xhash = Diffast_misc.Xhash
module XML = Diffast_misc.XML
module Otree = Diffast_misc.Otree
module UID = Diffast_misc.UID
module GI = Diffast_misc.GIndex
module Path = Diffast_misc.Path
module Storage = Diffast_misc.Storage
module Binding = Diffast_misc.Binding
module Loc = Diffast_misc.Loc

module MID   = Moveid
module BID   = Binding.ID


module OutChannel = struct

  type t =
    | Pervasives of out_channel
    | XChannel of Xchannel.out_channel

  let of_pervasives ch = Pervasives ch
  let of_xchannel ch = XChannel ch

  let is_stdout = function
    | Pervasives ch -> ch = Stdlib.stdout
    | _ -> false

  let to_pervasives = function
    | Pervasives ch -> ch
    | _ -> failwith "OutChannel.to_pervasives"

  let to_xchannel = function
    | XChannel ch -> ch
    | _ -> failwith "OutChannel.to_xchannel"

  let close = function
    | Pervasives ch -> Stdlib.close_out ch
    | XChannel ch -> ch#close

end


class type node_data_t_shared = object ('self)
  inherit Otree.data2

  method source_fid       : string
  method set_source_fid   : string -> unit

  method _digest      : Xhash.t option
  method digest       : Xhash.t option
  method set_digest   : Xhash.t -> unit
  method _set_digest  : Xhash.t -> unit
  method reset_digest : unit

  method label           : string
  method _label          : Obj.t
  method is_compatible_with : ?weak:bool -> 'self -> bool
  method relabel_allowed    : 'self -> bool
  method quasi_eq           : 'self -> bool
  method to_be_notified  : bool

  method eq             : 'self -> bool (* label *)
  method equals         : 'self -> bool (* label and digest *)
  method subtree_equals : 'self -> bool (* label and _digest (subtree) *)

  method set_loc : Loc.t -> unit
  method src_loc : Loc.t

  method to_rep    : string
  method to_string : string

  method feature : Obj.t * Xhash.t option

  method to_elem_data : string * (string * string) list * string

  method is_anonymous : bool

  method is_named           : bool
  method is_named_orig      : bool

  method get_name           : string
  method get_orig_name      : string
  method get_stripped_name  : string

  method _stripped_label    : Obj.t
  method _stripped_orig_label : Obj.t

  method _anonymized_label  : Obj.t
  method _anonymized2_label : Obj.t
  method _anonymized3_label : Obj.t

  method is_partition       : bool
  method is_boundary        : bool

  method set_mid         : MID.t -> unit
  method mid             : MID.t

  method binding     : Binding.t
  method bindings    : Binding.t list

  method orig_to_elem_data_for_eq    : string * (string * string) list * string


(* for delta *)
  method to_elem_data_for_delta      : string * (string * string) list * string
  method orig_to_elem_data_for_delta : string * (string * string) list * string
  method elem_name_for_delta         : string
  method orig_elem_name_for_delta    : string
  method elem_attrs_for_delta        : (string * string) list
  method orig_elem_attrs_for_delta   : (string * string) list

  method change_attr     : string -> string -> unit
  method delete_attr     : string -> unit
  method insert_attr     : string -> string -> unit


end (* of class type node_data_t_shared *)



type 'data node_t = (#node_data_t_shared as 'data) Otree.node2



class type [ 'node ] tree_t_shared = object ('self)
  inherit [ 'node ] Otree.otree2

  method parser_name               : string
  method get_digest                : 'node -> Xhash.t
  method add_to_bid_map            : BID.t -> BID.t -> unit
  method find_mapped_bids          : BID.t -> BID.t list
  method add_to_bid_tbl            : BID.t -> string -> unit
  method find_name_for_bid         : BID.t -> string
  method add_to_def_bid_tbl        : BID.t -> 'node -> unit
  method find_def_for_bid          : BID.t -> 'node
  method in_subtree_mutually       : 'node -> 'node -> bool
  method initial_subtree_to_rep    : 'node -> string
  method initial_to_rep            : string
  method set_source_path           : string -> unit
  method source_path               : string
  method set_ignored_regions       : (int * int) list -> unit
  method ignored_regions           : (int * int) list
  method get_units_to_be_notified  : 'node list
  method make_subtree_from_uid     : UID.t -> 'self
  method make_subtree_from_node    : 'node -> 'self
  method make_subtree_from_path    : Path.t -> 'self
  method make_subtree_copy         : ?find_hook:('node -> 'node -> unit) -> 'node -> 'self
  method dump_subtree_for_delta_ch : 'node -> 'node list -> Xchannel.out_channel -> unit
  method unparse_ch                : ?no_boxing:bool -> ?no_header:bool -> ?fail_on_error:bool -> OutChannel.t -> unit
  method extra_namespaces          : (string * string) list (* for subtrees in delta *)

end (* of class type tree_t_shared *)


class type ['tree] tree_factory_t = object
  method namespace_manager : XML.ns_manager
  method from_xnode        : XML.node     -> 'tree
  method from_file         : Storage.file -> 'tree
end
