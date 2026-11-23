import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonDecisionTree

/-!
# comparison_decision_tree_depth

Topic: algorithms   Node: 114d571a3748

Provenance: formalization of a published result. Source: arXiv:2611.26297

The depth of a comparison decision tree is the maximum number of comparisons along any path from the root to a leaf.
-/

/-- The depth (worst-case number of comparisons) of a comparison decision tree. -/
def comparison_decision_tree_depth {n : ℕ} {β : Type} : ComparisonDecisionTree n β → ℕ := fun
  | .leaf _ => 0
  | .branch _ _ l r => 1 + max (comparison_decision_tree_depth l) (comparison_decision_tree_depth r)
