import AFTD.Prelude
import AFTD.Kb.Tcs.NaeAnglePoly
import AFTD.Kb.Tcs.NaeAnglePolyLow
import AFTD.Kb.Tcs.NaeAnglePolyHigh

/-!
# nae_angle_poly_nonneg

Topic: quantum   Node: cf960debbc2e

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

For real x with 0 ≤ x ≤ 1/14, nae_angle_poly x is nonnegative.
-/

theorem nae_angle_poly_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 14) :
    0 ≤ nae_angle_poly x := by
  by_cases h : x ≤ 1 / 20
  · exact nae_angle_poly_low x hx0 h
  · exact nae_angle_poly_high x (le_of_not_ge h) hx
