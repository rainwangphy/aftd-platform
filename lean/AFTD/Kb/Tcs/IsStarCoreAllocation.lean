import AFTD.Prelude

/-!
# is_star_core_allocation

Topic: quantum   Node: 33f116cec13d

Provenance: formalization of a published result. Source: arXiv:2610.26814, Section 3.1

A tuple (b, a) is a valid qubit allocation for a star-core graph with k vertices and total qubit budget Q if the central block size b and all leaf block sizes a_i are positive integers and b + sum_i a_i = Q.
-/

/-- A valid qubit allocation for a star-core graph with k vertices and total budget Q. -/
def is_star_core_allocation (k Q : ℕ) (b : ℕ) (a : Fin (k - 1) → ℕ) : Prop :=
  1 ≤ b ∧ (∀ i, 1 ≤ a i) ∧ b + ∑ i, a i = Q
