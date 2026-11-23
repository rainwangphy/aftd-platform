import AFTD.Prelude
import AFTD.Kb.Tcs.RatPlanePoint

/-!
# rat_plane_point_dist

Topic: approximation   Node: 7f5d54ad70c1

Provenance: helper lemma. Sanity check of rat_plane_point: Euclidean distance formula.

The distance between the plane points of rational pairs p and q is sqrt((p1-q1)^2 + (p2-q2)^2).
-/

theorem rat_plane_point_dist (p q : ℚ × ℚ) :
    dist (rat_plane_point p) (rat_plane_point q) =
      Real.sqrt (((p.1 : ℝ) - q.1) ^ 2 + ((p.2 : ℝ) - q.2) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp [rat_plane_point, Fin.sum_univ_two, Real.dist_eq, sq_abs]
