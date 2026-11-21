import AFTD.Prelude

/-!
# op_2130_independent_failures_at_most_half

Topic: online_algorithms   Node: daf8afdc9ef7

Provenance: helper lemma. Independent-block counterexample to op_2130_path_greedy_fixed_time_tail

For 0 ≤ p ≤ 1 and a natural number N with Np ≥ 1, (1 − p)^N is at most one half.
-/

theorem op_2130_independent_failures_at_most_half (p : ℝ) (N : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : 1 ≤ (N : ℝ) * p) :
    (1 - p)^N ≤ (1 / 2 : ℝ) := by
  have hround : 1 - p ≤ Real.exp (-p) := by
    have h := Real.add_one_le_exp (-p)
    linarith
  have hpow : (1 - p)^N ≤ (Real.exp (-p))^N :=
    pow_le_pow_left₀ (sub_nonneg.mpr hp1) hround N
  rw [← Real.exp_nat_mul] at hpow
  have hexp : Real.exp ((N : ℝ) * (-p)) ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hone : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hhalf : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hone)
  exact le_trans hpow (le_trans hexp hhalf)
