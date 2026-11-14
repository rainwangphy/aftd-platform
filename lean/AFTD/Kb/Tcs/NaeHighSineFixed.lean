import AFTD.Prelude

/-!
# nae_high_sine_fixed

Topic: quantum   Node: 47e76f5db6f7

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

The sine of 2π/5 is at least √8/3.
-/

theorem nae_high_sine_fixed : Real.sqrt 8 / 3 ≤ Real.sin (2 * Real.pi / 5) := by
  have hsqrt : 0 ≤ Real.sqrt 8 := Real.sqrt_nonneg _
  have hsqrt8 : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hsqrt5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrt5pos : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hs5 : (19 / 9 : ℝ) ≤ Real.sqrt 5 := by nlinarith
  have hcosid : Real.cos (Real.pi / 5) = 2 * Real.cos (Real.pi / 10) ^ 2 - 1 := by
    have h := Real.cos_two_mul (Real.pi / 10)
    have heq : 2 * (Real.pi / 10) = Real.pi / 5 := by ring
    rw [heq] at h
    exact h
  have hcos := Real.cos_pi_div_five
  have hsin : Real.sin (2 * Real.pi / 5) = Real.cos (Real.pi / 10) := by
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    ring
  have hsinpos : 0 ≤ Real.sin (2 * Real.pi / 5) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  nlinarith [hsqrt8, hcosid, hcos, hsin]
