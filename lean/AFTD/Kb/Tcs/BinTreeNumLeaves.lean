import AFTD.Prelude
import AFTD.Kb.Tcs.BinTree

/-!
# bin_tree_num_leaves

Topic: graphs   Node: 84347fce2685

Provenance: formalization of a published result. Source: arXiv:2611.19659, Section 2

The function bin_tree_num_leaves computes the number of leaves in an ordered full binary tree: 1 for a leaf, and bin_tree_num_leaves l + bin_tree_num_leaves r for a node with left child l and right child r.
-/

/-- Number of leaves in an ordered full binary tree. -/
def bin_tree_num_leaves : BinTree → ℕ
  | .leaf => 1
  | .node l r => bin_tree_num_leaves l + bin_tree_num_leaves r
