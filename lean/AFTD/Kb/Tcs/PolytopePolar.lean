import AFTD.Prelude

/-!
# polytope_polar

Topic: combinatorics   Node: 28051c442312

Provenance: formalization of a published result. Source: arXiv:2611.08819 Section 1; Batyrev 1994

The polar polytope of a subset P of ℝ^d is the set of all vectors y in ℝ^d such that for every x in P, the standard inner product of x and y is at least -1.
-/

open scoped BigOperators in
/-- The polar polytope of P ⊆ ℝ^d is the set of points y with ∑ x_i y_i ≥ -1 for all x ∈ P. -/
def polytope_polar {d : ℕ} (P : Set (Fin d → ℝ)) : Set (Fin d → ℝ) := {y : Fin d → ℝ | ∀ x ∈ P, -1 ≤ ∑ i, x i * y i}
