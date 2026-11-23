import AFTD.Prelude
import AFTD.Kb.Tcs.RatSegmentsUnion
import AFTD.Kb.Tcs.RatPlanePoint

/-!
# rat_segments_union_point

Topic: approximation   Node: 45674e6605fb

Provenance: helper lemma. Sanity check of rat_segments_union: a degenerate segment is a point.

The union of the single degenerate segment from p to p is the one-point set {p}.
-/

theorem rat_segments_union_point (p : ℚ × ℚ) :
    rat_segments_union [(p, p)] = {rat_plane_point p} := by
  simp [rat_segments_union]
