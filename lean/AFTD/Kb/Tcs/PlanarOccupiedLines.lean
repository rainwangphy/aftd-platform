import AFTD.Prelude

/-!
# planar_occupied_lines

Topic: combinatorics   Node: 1bddcf7fb07b

Provenance: formalization of a published result. Source: arXiv:2610.38864 Section 1 and Section 3

The number of occupied parallel lines meeting a finite planar set A in the direction orthogonal to u is the number of distinct values of the inner product ⟪p, u⟫ for p ∈ A.
-/

/-- The number of affine lines perpendicular to u that meet A. -/
noncomputable def planar_occupied_lines (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (u : EuclideanSpace ℝ (Fin 2)) : ℕ := (A.image (fun p => inner ℝ p u)).card
