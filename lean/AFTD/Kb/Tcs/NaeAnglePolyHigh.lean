import AFTD.Prelude
import AFTD.Kb.Tcs.NaeAnglePoly

/-!
# nae_angle_poly_high

Topic: quantum   Node: 5a57d30ae270

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

For real x with 1/20 ≤ x ≤ 1/14, nae_angle_poly x is nonnegative.
-/

theorem nae_angle_poly_high (x : ℝ) (hx0 : 1 / 20 ≤ x) (hx : x ≤ 1 / 14) :
    0 ≤ nae_angle_poly x := by
  let a : ℝ := (140 * x - 7) / 3
  let b : ℝ := (10 - 140 * x) / 3
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hpos : 0 ≤
      142509918726743659 * b^11 + 1151878116961806815 * a*b^10 +
      5315499883836256450 * a^2*b^9 + 18904695335091016500 * a^3*b^8 +
      51180999291745693125 * a^4*b^7 + 99372532206124734375 * a^5*b^6 +
      134778483993429609375 * a^6*b^5 + 126197568178586953125 * a^7*b^4 +
      79993288283327343750 * a^8*b^3 + 32822354439847656250 * a^9*b^2 +
      7880130761357421875 * a^10*b + 841883855810546875 * a^11 := by positivity
  have hid : (96549157373046875 : ℝ) * nae_angle_poly x =
      142509918726743659 * b^11 + 1151878116961806815 * a*b^10 +
      5315499883836256450 * a^2*b^9 + 18904695335091016500 * a^3*b^8 +
      51180999291745693125 * a^4*b^7 + 99372532206124734375 * a^5*b^6 +
      134778483993429609375 * a^6*b^5 + 126197568178586953125 * a^7*b^4 +
      79993288283327343750 * a^8*b^3 + 32822354439847656250 * a^9*b^2 +
      7880130761357421875 * a^10*b + 841883855810546875 * a^11 := by
    dsimp [a, b, nae_angle_poly]
    ring
  nlinarith
