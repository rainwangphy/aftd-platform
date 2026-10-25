import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingSequenceAlpha
import AFTD.Kb.GameTheoryEconomics.IsRecursivelyBalanced

/-!
# recursively_balanced_alpha

Topic: fair_division   Node: fe68fa4d4383

Provenance: formalization of a published result. Source: arXiv:2610.23686, Sec. 6

The universal EF1 approximation factor α_RB for recursively balanced picking sequences is the infimum over all recursively balanced sequences with at least two agents of their guaranteed EF1 factor.
-/

/-- The universal EF1 approximation factor α_RB for all recursively balanced picking sequence mechanisms. -/
noncomputable def recursively_balanced_alpha : ℝ :=
  sInf {y : ℝ | ∃ (n : ℕ) (seq : List (Fin n)),
    is_recursively_balanced n seq ∧ 2 ≤ n ∧ y = picking_sequence_alpha n seq}
