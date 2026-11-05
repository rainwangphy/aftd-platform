import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsIdenticallyOrdered
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# is_identically_ordered_zero

Topic: fair_division   Node: 9b78f8456fd5

Provenance: helper lemma. arXiv:2611.04884, Section 2, page 8

The zero cost profile where all agents have cost zero for all chores is identically ordered.
-/

/-- The zero cost function profile is identically ordered. -/
lemma is_identically_ordered_zero (m n : ℕ) :
    is_identically_ordered (fun (_ : Fin n) (_ : Fin m) => (0 : ℝ)) := by
  intro i a b hab
  exact le_refl 0
