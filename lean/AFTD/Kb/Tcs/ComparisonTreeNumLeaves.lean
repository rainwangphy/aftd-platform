import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTree

/-!
# comparison_tree_num_leaves

Topic: algorithms   Node: 7cc733ec46ba

Provenance: formalization of a published result. Source: arXiv:2610.18740, Section 5

The number of leaves in a comparison decision tree is 1 for a leaf, and the sum of the leaf counts of its left and right subtrees for an internal branch.
-/

/-- The number of leaves in a comparison decision tree. -/
def comparison_tree_num_leaves {n : ℕ} : ComparisonTree n → ℕ
  | .leaf _ => 1
  | .branch _ _ l r => comparison_tree_num_leaves l + comparison_tree_num_leaves r
