import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTree

/-!
# comparison_tree_depth

Topic: algorithms   Node: b9539d5f442c

Provenance: formalization of a published result. Source: arXiv:2610.18740 Sec. 3.1

The depth of a comparison decision tree is the maximum number of comparisons along any branch from the root to a leaf.
-/

/-- The depth of a comparison decision tree, representing its worst-case comparison cost. -/
def comparison_tree_depth {n : ℕ} : ComparisonTree n → ℕ := fun
  | .leaf _ => 0
  | .branch _ _ l r => 1 + max (comparison_tree_depth l) (comparison_tree_depth r)
