import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.ComparisonDecisionTree
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# comparison_decision_tree_eval

Topic: algorithms   Node: 4715bc1d4cb4

Provenance: formalization of a published result. Source: arXiv:2611.26297

Evaluation of a comparison decision tree on an input sequence v : Fin n → α over a linear order α, branching left if v i < v j and right otherwise until reaching a leaf.
-/

/-- Evaluates a comparison decision tree on a linearly ordered sequence of values. -/
def comparison_decision_tree_eval {n : ℕ} {β : Type} {α : Type*} [LinearOrder α]
    (v : Fin n → α) : ComparisonDecisionTree n β → β := fun
  | .leaf ans => ans
  | .branch i j l r =>
      if v i < v j then comparison_decision_tree_eval v l else comparison_decision_tree_eval v r
