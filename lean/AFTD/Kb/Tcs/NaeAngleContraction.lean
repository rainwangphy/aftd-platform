import AFTD.Prelude
import AFTD.Kb.Tcs.NaeSineContraction

/-!
# nae_angle_contraction

Topic: quantum   Node: 5032e484b04a

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

For 0 ≤ θ ≤ π, arccos(1−(4/9)(1−cos θ)²) ≤ 15θ/16.
-/

theorem nae_angle_contraction (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ Real.pi) :
    Real.arccos (1 - (4 / 9 : ℝ) * (1 - Real.cos θ) ^ 2) ≤
      (15 / 16 : ℝ) * θ := by
  have hs := nae_sine_contraction (θ / 2) (by linarith) (by linarith)
  have hs0 : 0 ≤ Real.sin ((15 / 16 : ℝ) * (θ / 2)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc0 : 0 ≤ Real.sqrt 8 / 3 * Real.sin (θ / 2) ^ 2 := by positivity
  have hsq : (Real.sqrt 8 / 3) ^ 2 = (8 / 9 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  have hsquared := mul_self_le_mul_self hc0 hs
  have hsquared' : (8 / 9 : ℝ) * Real.sin (θ / 2) ^ 4 ≤
      Real.sin ((15 / 16 : ℝ) * (θ / 2)) ^ 2 := by
    calc
      (8 / 9 : ℝ) * Real.sin (θ / 2) ^ 4 =
          (Real.sqrt 8 / 3 * Real.sin (θ / 2) ^ 2) ^ 2 := by rw [← hsq]; ring
      _ ≤ Real.sin ((15 / 16 : ℝ) * (θ / 2)) ^ 2 := by simpa [pow_two] using hsquared
  have hcos1 : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul (θ / 2)
    have hid : 2 * (θ / 2) = θ := by ring
    rw [hid] at h
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hcos2 : Real.cos ((15 / 16 : ℝ) * θ) =
      1 - 2 * Real.sin ((15 / 16 : ℝ) * (θ / 2)) ^ 2 := by
    have h := Real.cos_two_mul ((15 / 16 : ℝ) * (θ / 2))
    have hid : 2 * ((15 / 16 : ℝ) * (θ / 2)) = (15 / 16 : ℝ) * θ := by ring
    rw [hid] at h
    nlinarith [Real.sin_sq_add_cos_sq ((15 / 16 : ℝ) * (θ / 2))]
  have hcomp : Real.cos ((15 / 16 : ℝ) * θ) ≤
      1 - (4 / 9 : ℝ) * (1 - Real.cos θ) ^ 2 := by
    rw [hcos1, hcos2]
    nlinarith [hsquared']
  have hanti := Real.arccos_le_arccos hcomp
  rw [Real.arccos_cos (by positivity) (by nlinarith [Real.pi_pos])] at hanti
  exact hanti
