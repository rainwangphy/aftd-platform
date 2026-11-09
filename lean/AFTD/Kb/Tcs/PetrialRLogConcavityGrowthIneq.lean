import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# petrial_R_log_concavity_growth_ineq

Topic: combinatorics   Node: fd60e3a46197

Provenance: helper lemma. arXiv:2611.07503 Theorem 8

For every natural number m ≥ 4, (441 * m ^ 2 + 525 * m + 24) * 2 ^ m < 16 * 11 ^ m.
-/

/-- The growth inequality (441 * m^2 + 525 * m + 24) * 2^m < 16 * 11^m for m >= 4 used in the proof of Theorem 8. -/
theorem petrial_R_log_concavity_growth_ineq (m : ℕ) (hm : 4 ≤ m) :
    (441 * m ^ 2 + 525 * m + 24) * 2 ^ m < 16 * 11 ^ m := by
  have hfac : ∀ k : ℕ, 441 * k ^ 2 + 525 * k + 24 = (21 * k + 1) * (21 * k + 24) := by
    intro k; ring
  have hstep : ∀ k : ℕ, 1 ≤ k →
      2 * ((21 * (k + 1) + 1) * (21 * (k + 1) + 24))
        ≤ 11 * ((21 * k + 1) * (21 * k + 24)) := by
    intro k hk
    nlinarith [sq_nonneg (k:ℤ), hk]
  have key : ∀ k : ℕ, 4 ≤ k →
      (441 * k ^ 2 + 525 * k + 24) * 2 ^ k * 11 ^ 4 ≤ 9180 * 16 * 11 ^ k := by
    intro k hk
    refine Nat.le_induction ?base ?step k hk
    · norm_num
    · intro n hn ih
      rw [hfac n] at ih
      rw [hfac (n+1)]
      rw [pow_succ, pow_succ]
      have hs : 2 * ((21 * (n + 1) + 1) * (21 * (n + 1) + 24))
          ≤ 11 * ((21 * n + 1) * (21 * n + 24)) := hstep n (by omega)
      calc (21 * (n + 1) + 1) * (21 * (n + 1) + 24) * (2 ^ n * 2) * 11 ^ 4
          = (2 * ((21 * (n + 1) + 1) * (21 * (n + 1) + 24))) * (2 ^ n * 11 ^ 4) := by ring
        _ ≤ (11 * ((21 * n + 1) * (21 * n + 24))) * (2 ^ n * 11 ^ 4) := by
              exact Nat.mul_le_mul_right _ hs
        _ = 11 * ((21 * n + 1) * (21 * n + 24) * 2 ^ n * 11 ^ 4) := by ring
        _ ≤ 11 * (9180 * 16 * 11 ^ n) := by
              exact Nat.mul_le_mul_left 11 ih
        _ = 9180 * 16 * (11 ^ n * 11) := by ring
  have hconst : 9180 * 16 < 16 * 11 ^ 4 := by norm_num
  have h1 : (441 * m ^ 2 + 525 * m + 24) * 2 ^ m * 11 ^ 4 < (16 * 11 ^ 4) * 11 ^ m := by
    calc (441 * m ^ 2 + 525 * m + 24) * 2 ^ m * 11 ^ 4
        ≤ 9180 * 16 * 11 ^ m := key m hm
      _ < (16 * 11 ^ 4) * 11 ^ m := Nat.mul_lt_mul_of_pos_right hconst (pow_pos (by norm_num) m)
  rw [show (16 * 11 ^ 4) * 11 ^ m = (16 * 11 ^ m) * 11 ^ 4 by ring] at h1
  exact Nat.lt_of_mul_lt_mul_right h1
