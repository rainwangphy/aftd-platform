import AFTD.Prelude
import AFTD.Kb.Tcs.MinTriangleArea
import AFTD.Kb.Tcs.IsUnitSquareConvexPointSet

/-!
# unit_square_min_triangle_sup

Topic: combinatorics   Node: 73008a9e8585

Provenance: formalization of a published result. Source: arXiv:2611.33233, Section 1

For each natural number n, unit_square_min_triangle_sup n is the supremum in ℝ of min_triangle_area P over all finite sets P : Finset (Fin 2 → ℝ) with cardinality n satisfying is_unit_square_convex_point_set P.
-/

/-- The supremum of minimum triangle areas over all n-point subsets in convex position in the unit square. -/
noncomputable def unit_square_min_triangle_sup (n : ℕ) : ℝ := sSup { m : ℝ | ∃ P : Finset (Fin 2 → ℝ), P.card = n ∧ is_unit_square_convex_point_set P ∧ m = min_triangle_area P }
