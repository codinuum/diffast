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


class c = object

(* id generators *)
  val moveid_generator = new Moveid.generator
  method moveid_generator = moveid_generator

(* flags *)
  val mutable viewer_flag = false
  val mutable check_flag  = false
  val mutable dots_flag   = false
  val mutable dist_flag   = false

  (* algo *)
  val mutable group_relabels_flag          = false
  val mutable lock_matches_flag            = false
  val mutable lower_ee_flag                = false
  val mutable multi_node_match_flag        = true
  val mutable multiple_classification_flag = false
  val mutable no_enclave_elim_flag         = false
  val mutable no_moves_flag                = false
  val mutable no_glue_flag                 = false
  val mutable simple_glue_flag             = false
  val mutable no_movrels_flag              = false
  val mutable no_odd_relabel_elim_flag     = false
  val mutable prematch_early_resolve_flag  = false
  val mutable prematch_flag                = true
  val mutable preprune_flag                = true
  val mutable shrink_moves_flag            = true
  val mutable trust_tree_matcher_flag      = true
  val mutable use_adjacency_matches_flag   = true
  val mutable no_unnamed_node_move_flag    = false
  val mutable conservative_flag            = true
  val mutable ignore_move_of_unordered_flag = false
  val mutable ignore_non_orig_relabel_flag = false

  val mutable rename_rectification_level = 2 (* 0: no rr, 1: rru, 2: rru+rrd, 3: rru+rrd(strict) *)
(* *)

  val mutable dump_size_threshold = 16

  val mutable conflicting_pairs_threshold            = 2
  val mutable hard_tree_size_limit                   = 1500
  val mutable mapped_neighbours_difference_threshold = 0.8
  val mutable match_algo_threshold                   = 512 (* for selecting match_trees impl. *)
  val mutable moderate_nchildren_threshold           = Const.default_moderate_nchildren_threshold
  val mutable movrel_ratio_threshold                 = 0.5
  val mutable movrel_stability_threshold             = 0.3
  val mutable pp_anonymized_match_threshold          = 0.5
  val mutable pp_relabel_criteria                    = 0.8
  val mutable prematch_cands_threshold               = 4
  val mutable prematch_subtree_cands_threshold       = 16
  val mutable preprune_threshold                     = 16
  val mutable prune_threshold                        = 1 (* any subtree of size < !prune_threshold may not be pruned *)
  val mutable subtree_match_ratio_threshold          = 0.6 (* must be > 0.5 *)
  val mutable tree_size_limit1                       = max_int
  val mutable tree_size_limit2                       = max_int
  val mutable tree_size_limit_percent                = 20 (* set in the initializer *)
  val mutable tree_size_limit_percent_default        = 20 (* maximum size of two intermediate subtrees (percent) *)
  val mutable tree_size_threshold                    = 128
  val mutable subtree_match_threshold                = 0 (* for multiple_subtree_matches *)


  method viewer_flag = viewer_flag
  method set_viewer_flag = viewer_flag <- true
  method clear_viewer_flag = viewer_flag <- false

  method check_flag = check_flag
  method set_check_flag = check_flag <- true
  method clear_check_flag = check_flag <- false

  method dots_flag = dots_flag
  method set_dots_flag = dots_flag <- true
  method clear_dots_flag = dots_flag <-false

  method dist_flag = dist_flag
  method set_dist_flag = dist_flag <- true
  method clear_dist_flag = dist_flag <-false


  (* algorithm *)
  method no_enclave_elim_flag = no_enclave_elim_flag
  method set_no_enclave_elim_flag = no_enclave_elim_flag <- true
  method clear_no_enclave_elim_flag = no_enclave_elim_flag <- false

  method no_odd_relabel_elim_flag = no_odd_relabel_elim_flag
  method set_no_odd_relabel_elim_flag = no_odd_relabel_elim_flag <- true
  method clear_no_odd_relabel_elim_flag = no_odd_relabel_elim_flag <- false

  method rename_rectification_level = rename_rectification_level
  method set_rename_rectification_level lv = rename_rectification_level <- lv

  method no_moves_flag = no_moves_flag
  method set_no_moves_flag = no_moves_flag <- true
  method clear_no_moves_flag = no_moves_flag <- false

  method no_glue_flag = no_glue_flag
  method set_no_glue_flag = no_glue_flag <- true
  method clear_no_glue_flag = no_glue_flag <- false

  method simple_glue_flag = simple_glue_flag
  method set_simple_glue_flag = simple_glue_flag <- true
  method clear_simple_glue_flag = simple_glue_flag <- false

  method group_relabels_flag = group_relabels_flag
  method set_group_relabels_flag = group_relabels_flag <- true
  method clear_group_relabels_flag = group_relabels_flag <- false

  method no_movrels_flag = no_movrels_flag
  method set_no_movrels_flag = no_movrels_flag <- true
  method clear_no_movrels_flag = no_movrels_flag <- false

  method prematch_flag = prematch_flag
  method set_prematch_flag = prematch_flag <- true
  method clear_prematch_flag = prematch_flag <- false

  method prematch_early_resolve_flag = prematch_early_resolve_flag
  method set_prematch_early_resolve_flag = prematch_early_resolve_flag <- true
  method clear_prematch_early_resolve_flag = prematch_early_resolve_flag <- false

  method preprune_flag = preprune_flag
  method set_preprune_flag = preprune_flag <- true
  method clear_preprune_flag = preprune_flag <- false

  method multi_node_match_flag = multi_node_match_flag
  method set_multi_node_match_flag = multi_node_match_flag <- true
  method clear_multi_node_match_flag = multi_node_match_flag <- false

  method lower_ee_flag = lower_ee_flag
  method set_lower_ee_flag = lower_ee_flag <- true
  method clear_lower_ee_flag = lower_ee_flag <- false

  method trust_tree_matcher_flag = trust_tree_matcher_flag
  method set_trust_tree_matcher_flag = trust_tree_matcher_flag <- true
  method clear_trust_tree_matcher_flag = trust_tree_matcher_flag <- false

  method multiple_classification_flag = multiple_classification_flag
  method set_multiple_classification_flag = multiple_classification_flag <- true
  method clear_multiple_classification_flag = multiple_classification_flag <- false

  method lock_matches_flag = lock_matches_flag
  method set_lock_matches_flag = lock_matches_flag <- true
  method clear_lock_matches_flag = lock_matches_flag <- false

  method shrink_moves_flag = shrink_moves_flag
  method set_shrink_moves_flag = shrink_moves_flag <- true
  method clear_shrink_moves_flag = shrink_moves_flag <- false

  method use_adjacency_matches_flag = use_adjacency_matches_flag
  method set_use_adjacency_matches_flag = use_adjacency_matches_flag <- true
  method clear_use_adjacency_matches_flag = use_adjacency_matches_flag <- false

  method no_unnamed_node_move_flag = no_unnamed_node_move_flag
  method set_no_unnamed_node_move_flag = no_unnamed_node_move_flag <- true
  method clear_no_unnamed_node_move_flag = no_unnamed_node_move_flag <- false

  method conservative_flag = conservative_flag
  method set_conservative_flag = conservative_flag <- true
  method clear_conservative_flag = conservative_flag <- false

  method ignore_move_of_unordered_flag = ignore_move_of_unordered_flag
  method set_ignore_move_of_unordered_flag = ignore_move_of_unordered_flag <- true
  method clear_ignore_move_of_unordered_flag = ignore_move_of_unordered_flag <- false

  method ignore_non_orig_relabel_flag = ignore_non_orig_relabel_flag
  method set_ignore_non_orig_relabel_flag = ignore_non_orig_relabel_flag <- true
  method clear_ignore_non_orig_relabel_flag = ignore_non_orig_relabel_flag <- false

(* *)

  method dump_size_threshold = dump_size_threshold
  method set_dump_size_threshold x = dump_size_threshold <- x

  method moderate_nchildren_threshold = moderate_nchildren_threshold
  method set_moderate_nchildren_threshold x = moderate_nchildren_threshold <- x

  method tree_size_threshold = tree_size_threshold
  method set_tree_size_threshold x = tree_size_threshold <- x

  method subtree_match_threshold = subtree_match_threshold
  method set_subtree_match_threshold x = subtree_match_threshold <- x

  method match_algo_threshold = match_algo_threshold
  method set_match_algo_threshold x = match_algo_threshold <- x

  method prematch_cands_threshold = prematch_cands_threshold
  method set_prematch_cands_threshold x = prematch_cands_threshold <- x

  method prematch_subtree_cands_threshold = prematch_subtree_cands_threshold
  method set_prematch_subtree_cands_threshold x = prematch_subtree_cands_threshold <- x

  method subtree_match_ratio_threshold = subtree_match_ratio_threshold
  method set_subtree_match_ratio_threshold x = subtree_match_ratio_threshold <- x

  method conflicting_pairs_threshold = conflicting_pairs_threshold
  method set_conflicting_pairs_threshold x = conflicting_pairs_threshold <- x

  method pp_relabel_criteria = pp_relabel_criteria
  method set_pp_relabel_criteria x = pp_relabel_criteria <- x

  method pp_anonymized_match_threshold = pp_anonymized_match_threshold
  method set_pp_anonymized_match_threshold x = pp_anonymized_match_threshold <- x

  method tree_size_limit1 = tree_size_limit1
  method set_tree_size_limit1 x = tree_size_limit1 <- x

  method tree_size_limit2 = tree_size_limit2
  method set_tree_size_limit2 x = tree_size_limit2 <- x

  method tree_size_limit_percent_default = tree_size_limit_percent_default
  method set_tree_size_limit_percent_default x = tree_size_limit_percent_default <- x

  method tree_size_limit_percent = tree_size_limit_percent
  method set_tree_size_limit_percent x = tree_size_limit_percent <- x

  method hard_tree_size_limit = hard_tree_size_limit
  method set_hard_tree_size_limit x = hard_tree_size_limit <- x

  method prune_threshold = prune_threshold
  method set_prune_threshold x = prune_threshold <- x

  method preprune_threshold = preprune_threshold
  method set_preprune_threshold x = preprune_threshold <- x

  method movrel_stability_threshold = movrel_stability_threshold
  method set_movrel_stability_threshold x = movrel_stability_threshold <- x

  method movrel_ratio_threshold = movrel_ratio_threshold
  method set_movrel_ratio_threshold x = movrel_ratio_threshold <- x

  method mapped_neighbours_difference_threshold = mapped_neighbours_difference_threshold
  method set_mapped_neighbours_difference_threshold x = mapped_neighbours_difference_threshold <- x

  initializer
    tree_size_limit_percent <- tree_size_limit_percent_default;

end (* of class Engine_options.c *)
