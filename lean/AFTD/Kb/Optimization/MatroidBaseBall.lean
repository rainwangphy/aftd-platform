import AFTD.Prelude

/-!
# matroid_base_ball

Topic: submodular   Node: 35bff3f23d85

Provenance: formalization of a published result. Source: arXiv:2611.27934, Section 4.2.1

For a matroid M, a basis B, and a radius r, the ball Ball_M(B, r) is the set of bases A of M such that |B \ A| ≤ r.
-/

/-- The metric ball of radius r around a basis B in a matroid M. -/
def matroid_base_ball {α : Type*} (M : Matroid α) (B : Set α) (r : ℕ) : Set (Set α) := {A | M.IsBase A ∧ (B \ A).ncard ≤ r}
