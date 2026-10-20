import AFTD.Prelude

/-!
# ordinal_profile_consistent

Topic: algorithms   Node: 439b09f1e127

Provenance: formalization of a published result. Source: arXiv:2610.23032 Section 4

Given a distance function d : V → V → ℝ and an ordinal profile represented as a family of linear orders π : V → LinearOrder V, π is consistent with d if for all i, j, k : V, whenever j < k according to the linear order π i, we have d(i, j) ≤ d(i, k).
-/

/-- An ordinal profile is consistent with a pseudometric d if preference implies smaller or equal distance. -/
def ordinal_profile_consistent {V : Type*} (d : V → V → ℝ) (π : V → LinearOrder V) : Prop :=
  ∀ i j k : V, @LT.lt V (π i).toLT j k → d i j ≤ d i k
