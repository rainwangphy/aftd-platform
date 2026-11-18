import AFTD.Prelude
import AFTD.Kb.Tcs.GeneralizedNumericalSemigroup
import AFTD.Kb.Tcs.GeneralizedNumericalSemigroupNonGapsBelowGaps

/-!
# generalized_numerical_semigroup_eta

Topic: combinatorics   Node: 4a8a820c10b3

Provenance: formalization of a published result. Source: arXiv:2611.20086 Section 6

For an element f in ℕ^d, η_f is the number of non-gaps below gaps of S that are bounded above by f in the pointwise partial order.
-/

/-- The number of non-gaps below gaps of S that are less than or equal to f. -/
noncomputable def generalized_numerical_semigroup_eta {d : ℕ} (S : GeneralizedNumericalSemigroup d) (f : Fin d → ℕ) : ℕ := by
  classical
  exact ((generalized_numerical_semigroup_non_gaps_below_gaps S).filter (fun s => s ≤ f)).card
