import AFTD.Prelude

/-!
# b3_core_ineq

Topic: graphs   Node: cb7718260118

Provenance: helper lemma. arXiv:2610.21388 (Stronger spectral bound for clique number), proof of Theorem 3.1 (the case n_1 ≥ n_2, (n_1,n_2) ≠ (1,1), cleared of denominators); serves b3_sqrt_trace_quotient_sq_le_clique_bound

For naturals a ≥ 2, 1 ≤ b ≤ a, c ≥ 1: (a^2 + b^2 - c^2 + 2(a+b+c)c + 3 - 2(a+b+c)) (a+c)^2 ≤ (a+b+c)^2 (a+c-1)^2.
-/

theorem b3_core_ineq (a b c : ℕ) (hb : 1 ≤ b) (hc : 1 ≤ c) (hab : b ≤ a) (h2 : 2 ≤ a) :
    ((a:ℝ)^2 + b^2 - c^2 + 2*(a+b+c)*c + 3 - 2*(a+b+c)) * ((a:ℝ)+c)^2
      ≤ ((a:ℝ)+b+c)^2 * ((a:ℝ)+c-1)^2 := by
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast h2
  have hb' : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hc' : (1:ℝ) ≤ c := by exact_mod_cast hc
  have hab' : (b:ℝ) ≤ a := by exact_mod_cast hab
  nlinarith [mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hb'), mul_nonneg (sub_nonneg.2 hc') (sub_nonneg.2 hb'),
    mul_nonneg (sub_nonneg.2 hab') (sub_nonneg.2 hb'), mul_nonneg (sub_nonneg.2 hab') (sub_nonneg.2 hc'),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hc') (sub_nonneg.2 hb')) (sub_nonneg.2 hc'),
    mul_nonneg (mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hb')) (sub_nonneg.2 hc'),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hab') (sub_nonneg.2 hb')) (sub_nonneg.2 hc')]
