import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# is_identically_ordered

Topic: fair_division   Node: 748af0080069

Provenance: formalization of a published result. Source: arXiv:2611.04884, Section 2, page 8

An instance of m chores and n agents with cost functions c is identically ordered (IDO) if for every agent i, the cost function c_i is non-increasing (antitone) with respect to chore index.
-/

/-- An instance of chores is identically ordered (IDO) if every agent's chore cost function is non-increasing. -/
def is_identically_ordered {m n : ℕ} (c : Fin n → Fin m → ℝ) : Prop := ∀ i : Fin n, Antitone (c i)
