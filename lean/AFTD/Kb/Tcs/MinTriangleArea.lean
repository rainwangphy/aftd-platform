import AFTD.Prelude
import AFTD.Kb.Tcs.TriangleArea

/-!
# min_triangle_area

Topic: combinatorics   Node: 9c477b46661d

Provenance: formalization of a published result. Source: arXiv:2611.33233, Section 1

For a finite point set P in ℝ², the minimum triangle area m(P) is the infimum of the areas of triangles formed by three distinct points of P.
-/

/-- The minimum area of a triangle determined by three distinct points in a finite set in ℝ². -/
noncomputable def min_triangle_area (P : Finset (Fin 2 → ℝ)) : ℝ := sInf { a : ℝ | ∃ p ∈ P, ∃ q ∈ P, ∃ r ∈ P, p ≠ q ∧ q ≠ r ∧ p ≠ r ∧ a = triangle_area p q r }
