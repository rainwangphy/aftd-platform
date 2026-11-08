import AFTD.Prelude
import AFTD.Kb.Tcs.Op491EventualThresholdLeOfStabilizes
import AFTD.Kb.Tcs.TwoFourCodeMaxCard
import AFTD.Kb.Tcs.TwoFourEventualThreshold

/-!
# op_491_threshold_le_two_q_minus_one_of_stabilizes

Topic: information   Node: bdcaa998aea0

Provenance: helper lemma. arXiv:2610.30613 Remark 6.1

If $A_q(n, \\{2,4\\}) = 1 + \\binom{n}{2}$ holds at $n = 2q - 1$, at $n = 2q$, and for all $n \\ge 2q + 1$, then the eventual length threshold satisfies $N_*(q) \\le 2q - 1$.
-/

/-- If stabilization holds at 2q-1, 2q, and all n ≥ 2q+1, then N_*(q) ≤ 2q - 1. -/
theorem op_491_threshold_le_two_q_minus_one_of_stabilizes (q : ℕ) (h_base : two_four_code_max_card q (2 * q - 1) = 1 + Nat.choose (2 * q - 1) 2) (h_next : two_four_code_max_card q (2 * q) = 1 + Nat.choose (2 * q) 2) (h_large : ∀ n ≥ 2 * q + 1, two_four_code_max_card q n = 1 + Nat.choose n 2) : two_four_eventual_threshold q ≤ 2 * q - 1 := by
  apply op_491_eventual_threshold_le_of_stabilizes
  intro n hn
  rcases lt_or_ge n (2 * q) with h | h
  · have hEq : n = 2 * q - 1 := by omega
    rw [hEq]
    exact h_base
  · rcases eq_or_lt_of_le h with hEq | hlt
    · rw [← hEq]
      exact h_next
    · exact h_large n (by omega)
