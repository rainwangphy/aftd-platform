import AFTD.Prelude

/-!
# ose_cube_scalar_certificate

Topic: algorithms   Node: 08bee75ec24d

Provenance: helper lemma. arXiv:2611.08546, Section 6.1; scalar certificate for the spherical embedding

For real p at least two and u between zero and one, four times p cubed times u squared times one minus u is at most (p minus one) times (p squared minus u squared) squared.
-/

theorem ose_cube_scalar_certificate (p u : ℝ) (hp : 2 ≤ p) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    4 * p^3 * u^2 * (1-u) ≤ (p-1) * (p^2-u^2)^2 := by
  have hp0 : 0 ≤ p := by linarith
  have hu2 : u^2 ≤ 1 := by nlinarith
  have ha : 0 ≤ 4 - 27*u^2*(1-u) := by
    have hv : 0 ≤ (3*u-2)^2 * (3*u+1) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith [hv]
  let t := p - 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hpol : 0 ≤ 27*t^5 + 243*t^4 + 794*t^3 + 1146*t^2 + 699*t + 115 := by positivity
  have hb : 0 ≤ 27*(p-1)*(p^2-1)^2 - 16*p^3 := by
    have heq : 27*(p-1)*(p^2-1)^2 - 16*p^3 =
        27*t^5 + 243*t^4 + 794*t^3 + 1146*t^2 + 699*t + 115 := by dsimp [t]; ring
    linarith
  have hsq : (p^2-1)^2 ≤ (p^2-u^2)^2 := by
    apply pow_le_pow_left₀ (by nlinarith) (by nlinarith) 2
  have hc : 0 ≤ (p-1) * ((p^2-u^2)^2 - (p^2-1)^2) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hsq)
  have hd : 0 ≤ p^3 * (4 - 27*u^2*(1-u)) :=
    mul_nonneg (pow_nonneg hp0 _) ha
  nlinarith [hb, hc, hd]
