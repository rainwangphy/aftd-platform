import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonDecisionTreeEval
import AFTD.Kb.Tcs.IsValidGuaranteedRollercoaster
import AFTD.Kb.Tcs.ComparisonDecisionTree

/-!
# comparison_tree_finds_guaranteed_rollercoaster

Topic: algorithms   Node: a716b0d5d0c2

Provenance: formalization of a published result. Source: arXiv:2611.26297 Sec. 4

A comparison decision tree T on n elements correctly finds a guaranteed-length k-rollercoaster if for every permutation σ of Fin n, the index subsequence returned by evaluating T on σ is a valid guaranteed-length k-rollercoaster.
-/

/-- A comparison tree finds a guaranteed k-rollercoaster if it outputs a valid guaranteed subsequence for every permutation. -/
def comparison_tree_finds_guaranteed_rollercoaster (k n : ℕ)
    (T : ComparisonDecisionTree n (List (Fin n))) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    is_valid_guaranteed_rollercoaster k n (fun i => σ i)
      (comparison_decision_tree_eval (fun i => σ i) T)
