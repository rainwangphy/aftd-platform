import AFTD.Prelude

/-!
# lower_convex_envelope

Topic: information   Node: 1f7230ffc084

Provenance: original. Related work: folklore

The lower convex envelope of a subset S ⊆ ℝ × ℝ evaluated at c is the infimum of y ∈ ℝ such that (c, y) lies in the convex hull of S.
-/

/-- Lower convex envelope of a point set S ⊆ ℝ² evaluated at c -/
noncomputable def lower_convex_envelope (S : Set (ℝ × ℝ)) (c : ℝ) : ℝ := sInf { y : ℝ | (c, y) ∈ convexHull ℝ S }
