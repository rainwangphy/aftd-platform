import AFTD.Prelude

/-!
# parallel_mw_two_pow_quadratic_bound

Topic: combinatorics   Node: 102048dec3f2

Provenance: helper lemma. Algebraic reduction for parallel_mw_ratio_decreasing_triple and OP-670.

For every natural a, the real inequality a²+a ≤ 2·2^a holds.
-/

theorem parallel_mw_two_pow_quadratic_bound (a : ℕ) : (a : ℝ)^2 + a ≤ 2*(2 : ℝ)^a := by
  have haux : ∀ n : ℕ, 2 ≤ n → (n : ℝ)^2 + n ≤ 2*(2 : ℝ)^n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hp := mul_nonneg (show 0 ≤ (n : ℝ)-2 by linarith) (show 0 ≤ (n : ℝ)+1 by positivity)
      rw [Nat.cast_succ, show (2 : ℝ)^(n+1) = 2^n*2 by rw [pow_succ]]
      nlinarith
  by_cases h : 2 ≤ a
  · exact haux a h
  · interval_cases a <;> norm_num
