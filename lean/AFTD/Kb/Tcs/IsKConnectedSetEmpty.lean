import AFTD.Prelude
import AFTD.Kb.Tcs.IsKConnectedSet
import AFTD.Kb.Tcs.MatroidConnectivity

/-!
# is_k_connected_set_empty

Topic: combinatorics   Node: b65d10f414a2

Provenance: formalization of a published result. Source: arXiv:2610.29979, Section 2

In every matroid $M$, the empty set is $k$-connected for all $k$.
-/

/-- The empty set is k-connected in every matroid for all k. -/
theorem is_k_connected_set_empty {α : Type*} (M : Matroid α) (k : ℕ) : IsKConnectedSet M k ∅ := by
  intro A _
  simp
