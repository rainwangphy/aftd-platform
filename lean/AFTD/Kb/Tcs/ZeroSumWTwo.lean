import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroSumW
import AFTD.Kb.Tcs.ZeroSumWGe
import AFTD.Kb.Tcs.ZeroSumWTwoLe

/-!
# zero_sum_w_two

Topic: combinatorics   Node: ac82b668fa4c

Provenance: formalization of a published result. Source: arXiv:2610.19965 (Proofs and disproofs of some conjectures on zero-sum problems), Theorem 1.2 (i). The case n = 2 of Question 3.1 (list entry OP-259).

For every r ≥ 1, w_r(2) = 2r + 1.
-/

theorem zero_sum_w_two (r : ℕ) (hr : 1 ≤ r) : zero_sum_w r 2 = ((2 * r + 1 : ℕ) : ℕ∞) := by
  have _ := hr
  have hge := zero_sum_w_ge r 2 (by norm_num)
  have hle := zero_sum_w_two_le r
  have heq : 2 * r * (2 - 1) + 1 = 2 * r + 1 := by omega
  rw [heq] at hge
  exact le_antisymm hle hge
