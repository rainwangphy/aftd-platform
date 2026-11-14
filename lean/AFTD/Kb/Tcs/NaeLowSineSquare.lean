import AFTD.Prelude

/-!
# nae_low_sine_square

Topic: quantum   Node: 73e2930bfffc

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

For 0 ≤ t ≤ 7π/16, sin²(t) ≤ 63/64.
-/

theorem nae_low_sine_square (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 7 * Real.pi / 16) :
    Real.sin t ^ 2 ≤ (63 / 64 : ℝ) := by
  have h16 : (1 / 8 : ℝ) ≤ Real.sin (Real.pi / 16) := by
    have h := Real.mul_le_sin (x := Real.pi / 16) (by positivity) (by linarith [Real.pi_pos])
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    convert h using 1 <;> field_simp <;> ring
  have hc : Real.cos (7 * Real.pi / 16) ≤ Real.cos t := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi ht0
    · linarith [Real.pi_pos]
    · exact ht
  have hid : Real.cos (7 * Real.pi / 16) = Real.sin (Real.pi / 16) := by
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    ring
  rw [hid] at hc
  have hcos : (1 / 8 : ℝ) ≤ Real.cos t := le_trans h16 hc
  have hsums := Real.sin_sq_add_cos_sq t
  nlinarith [sq_nonneg (Real.cos t - 1 / 8)]
