import AFTD.Prelude

/-!
# is_unit_square_convex_point_set

Topic: combinatorics   Node: 2da5c7f56f4e

Provenance: formalization of a published result. Source: arXiv:2611.33233, Section 1

For a finite set P of points in the plane represented as functions Fin 2 → ℝ, is_unit_square_convex_point_set P asserts that for every point p in P, p i ∈ Set.Icc (0 : ℝ) 1 for all i : Fin 2, and every point p in P is an extreme point of the convex hull of P over ℝ.
-/

/-- Predicate that a finite set of points P : Finset (Fin 2 → ℝ) lies in the unit square [0,1]² and is in convex position. -/
def is_unit_square_convex_point_set (P : Finset (Fin 2 → ℝ)) : Prop := (∀ p ∈ P, ∀ i : Fin 2, p i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ p ∈ P, p ∈ (convexHull ℝ (P : Set (Fin 2 → ℝ))).extremePoints ℝ)
