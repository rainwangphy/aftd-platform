import AFTD.Prelude

/-!
# rat_plane_point

Topic: approximation   Node: e7feeb9adfcf

Provenance: helper lemma. Geometry, helper for the polynomial-time statement of OP-2019 (arXiv:2611.24611 (Inapproximability of Euclidean Steiner Tree), Section 6.1, after Corollary 20 (open question: is planar Euclidean Cable Steiner Tree APX-hard or does it admit a PTAS?)).

The point of the Euclidean plane EuclideanSpace ℝ (Fin 2) with coordinates (x, y), for a pair (x, y) of rationals.
-/

/-- The point (x, y) of the Euclidean plane `EuclideanSpace ℝ (Fin 2)` given by a pair of rationals. -/
noncomputable def rat_plane_point (p : ℚ × ℚ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(p.1 : ℝ), (p.2 : ℝ)]
