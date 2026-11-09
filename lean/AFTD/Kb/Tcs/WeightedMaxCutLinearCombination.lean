import AFTD.Prelude

/-!
# weighted_max_cut_linear_combination

Topic: graphs   Node: c91cdd73930f

Provenance: helper lemma. arXiv:2611.05178 Section 3

For all real numbers W and M, the convex combination of (3/4)W + (3/16)M and W - M with weights 16/19 and 3/19 equals (15/19)W.
-/

/-- Linear combination identity combining the structural cut bound and the max-cut partition bound. -/
theorem weighted_max_cut_linear_combination (W M : ℝ) :
    (16 / 19 : ℝ) * ((3 / 4 : ℝ) * W + (3 / 16 : ℝ) * M) + (3 / 19 : ℝ) * (W - M) =
    (15 / 19 : ℝ) * W := by
  ring
