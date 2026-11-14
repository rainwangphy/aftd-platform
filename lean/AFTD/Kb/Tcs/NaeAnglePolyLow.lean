import AFTD.Prelude
import AFTD.Kb.Tcs.NaeAnglePoly

/-!
# nae_angle_poly_low

Topic: quantum   Node: fc9e4642344c

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

For real x with 0 ≤ x ≤ 1/20, nae_angle_poly x is nonnegative.
-/

theorem nae_angle_poly_low (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 20) :
    0 ≤ nae_angle_poly x := by
  let a : ℝ := 20 * x
  let b : ℝ := 1 - 20 * x
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hpos : 0 ≤
      10986328125 * b^11 + 91142578125 * a*b^10 +
      337324218750 * a^2*b^9 + 732297656250 * a^3*b^8 +
      1030613671875 * a^4*b^7 + 980164515625 * a^5*b^6 +
      636255065625 * a^6*b^5 + 277841341875 * a^7*b^4 +
      78426497500 * a^8*b^3 + 13370991150 * a^9*b^2 +
      1283373165 * a^10*b + 72072013 * a^11 := by positivity
  have hid : (48828125 : ℝ) * nae_angle_poly x =
      10986328125 * b^11 + 91142578125 * a*b^10 +
      337324218750 * a^2*b^9 + 732297656250 * a^3*b^8 +
      1030613671875 * a^4*b^7 + 980164515625 * a^5*b^6 +
      636255065625 * a^6*b^5 + 277841341875 * a^7*b^4 +
      78426497500 * a^8*b^3 + 13370991150 * a^9*b^2 +
      1283373165 * a^10*b + 72072013 * a^11 := by
    dsimp [a, b, nae_angle_poly]
    ring
  nlinarith
