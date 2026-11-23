import AFTD.Prelude
import AFTD.Kb.Tcs.RatPlanePoint

/-!
# rat_segments_union

Topic: approximation   Node: a815f81c12b7

Provenance: helper lemma. Geometry, helper for the polynomial-time statement of OP-2019 (arXiv:2611.24611 (Inapproximability of Euclidean Steiner Tree), Section 6.1, after Corollary 20 (open question: is planar Euclidean Cable Steiner Tree APX-hard or does it admit a PTAS?)); a cable is a connected finite union of closed segments (Definition 5).

For a list S of pairs of rational points of the plane, the subset of EuclideanSpace ℝ (Fin 2) that is the union, over the pairs (a, b) in S, of the closed line segment from the point a to the point b.
-/

/-- The union in the plane of the closed segments listed in `S` (rational endpoints). -/
noncomputable def rat_segments_union (S : List ((ℚ × ℚ) × (ℚ × ℚ))) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ s ∈ S, segment ℝ (rat_plane_point s.1) (rat_plane_point s.2)
