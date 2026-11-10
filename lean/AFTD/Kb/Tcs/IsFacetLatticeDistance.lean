import AFTD.Prelude

/-!
# is_facet_lattice_distance

Topic: combinatorics   Node: 18ca30568d5e

Provenance: formalization of a published result. Source: scout/2611-08819-reflexive-polytopes-can-have-doubly-exponentially-many-vert.md:241

A positive integer h is the lattice distance of a facet F of a polytope B in ℝ^n from the origin if there exists a primitive integral vector a in ℤ^n such that for all x in B, ⟨a, x⟩ ≥ -h, and for all x in F, ⟨a, x⟩ = -h.
-/

open scoped BigOperators in
/-- A positive integer h is the lattice distance of a facet F of B from the origin if F is defined by a primitive inward normal functional at level -h. -/
def is_facet_lattice_distance {n : ℕ} (B F : Set (Fin n → ℝ)) (h : ℕ) : Prop := 0 < h ∧
  ∃ a : Fin n → ℤ,
    Finset.gcd Finset.univ a = 1 ∧
    (∀ x ∈ B, - (h : ℝ) ≤ ∑ i, (a i : ℝ) * x i) ∧
    (∀ x ∈ F, ∑ i, (a i : ℝ) * x i = - (h : ℝ))
