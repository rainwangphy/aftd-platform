import AFTD.Prelude
import AFTD.Kb.Tcs.RatPlanePoint

/-!
# rat_segments_length

Topic: approximation   Node: 322b08807472

Provenance: helper lemma. Objective, helper for the polynomial-time statement of OP-2019 (arXiv:2611.24611 (Inapproximability of Euclidean Steiner Tree), Section 6.1, after Corollary 20 (open question: is planar Euclidean Cable Steiner Tree APX-hard or does it admit a PTAS?)).

For a list S of pairs of rational points of the plane, the real number that is the sum over the pairs (a, b) in S (with multiplicity) of the Euclidean distance between the points a and b.
-/

/-- The total Euclidean length of the segments listed in `S`. -/
noncomputable def rat_segments_length (S : List ((ℚ × ℚ) × (ℚ × ℚ))) : ℝ :=
  (S.map fun s => dist (rat_plane_point s.1) (rat_plane_point s.2)).sum
