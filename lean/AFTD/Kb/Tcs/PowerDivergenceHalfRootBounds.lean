import AFTD.Prelude

/-!
# power_divergence_half_root_bounds

Topic: information   Node: 33975423fe0a

Provenance: helper lemma. Helper for the refutations of subadditivity of mutual f_β-information, arXiv:2610.21231 (On the subadditivity of mutual f-information): rational bounds on real roots.

For x ≥ 0 and b ≥ 0, if a^2 ≤ x ≤ b^2 then a ≤ x^(1/2) ≤ b.
-/

theorem power_divergence_half_root_bounds (x a b : ℝ) (hx : 0 ≤ x) (hb : 0 ≤ b)
    (h1 : a ^ 2 ≤ x) (h2 : x ≤ b ^ 2) : a ≤ x ^ ((1 : ℝ) / 2) ∧ x ^ ((1 : ℝ) / 2) ≤ b := by
  have ht0 : 0 ≤ x ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx _
  have ht : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    rw [show (1 : ℝ) / 2 = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hx (by norm_num)
  constructor
  · exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) ht0 (by rw [ht]; exact h1)
  · exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb (by rw [ht]; exact h2)
