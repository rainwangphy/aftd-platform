import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTree
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# comparison_tree_eval

Topic: algorithms   Node: fe073690b9c9

Provenance: formalization of a published result. Source: arXiv:2610.18740 Sec. 3.1

Given an assignment v : Fin n → α of values in a linearly ordered type α, evaluate a comparison tree: on a leaf leaf ans, return the index ans; on a branch branch i j l r, if v i < v j strictly, recursively evaluate the left subtree l on v, otherwise recursively evaluate the right subtree r on v.
-/

/-- Evaluation of a comparison decision tree on an assignment of linearly ordered values. -/
def comparison_tree_eval {n : ℕ} {α : Type*} [LinearOrder α] (v : Fin n → α) :
    ComparisonTree n → Fin n := fun
  | .leaf ans => ans
  | .branch i j l r =>
      if v i < v j then comparison_tree_eval v l else comparison_tree_eval v r
