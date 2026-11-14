import AFTD.Prelude
import AFTD.Kb.Tcs.NaeSinScale
import AFTD.Kb.Tcs.NaeLowSineSquare
import AFTD.Kb.Tcs.NaeHighSineFixed

/-!
# nae_sine_contraction

Topic: quantum   Node: 45452444734b

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

For 0 ≤ t ≤ π/2, (√8/3) sin²(t) ≤ sin(15t/16).
-/

theorem nae_sine_contraction (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ Real.pi / 2) :
    Real.sqrt 8 / 3 * Real.sin t ^ 2 ≤ Real.sin ((15 / 16 : ℝ) * t) := by
  have hs0 : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos])
  have hc0 : 0 ≤ Real.sqrt 8 / 3 := by positivity
  have hc2 : (Real.sqrt 8 / 3) ^ 2 = (8 / 9 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  by_cases hsmall : t ≤ 7 * Real.pi / 16
  · have hsq := nae_low_sine_square t ht0 hsmall
    have hprod := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.sqrt 8 / 3))
    rw [hc2] at hprod
    have hcoeff : Real.sqrt 8 / 3 * Real.sin t ≤ (15 / 16 : ℝ) := by
      nlinarith [sq_nonneg (Real.sqrt 8 / 3 * Real.sin t - (15 / 16 : ℝ))]
    have hmul := mul_le_mul_of_nonneg_right hcoeff hs0
    have hscale := nae_sin_scale t ht0 (by linarith [Real.pi_pos])
    nlinarith
  · have hlarge : 7 * Real.pi / 16 ≤ t := le_of_not_ge hsmall
    have hmono : Real.sin (2 * Real.pi / 5) ≤ Real.sin ((15 / 16 : ℝ) * t) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · linarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    have hsq := Real.sin_sq_le_one t
    have hmul := mul_le_mul_of_nonneg_left hsq hc0
    nlinarith [nae_high_sine_fixed]
