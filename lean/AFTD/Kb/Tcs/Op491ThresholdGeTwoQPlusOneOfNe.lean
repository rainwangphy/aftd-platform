import AFTD.Prelude
import AFTD.Kb.Tcs.Op491ThresholdGtOfNe
import AFTD.Kb.Tcs.TwoFourCodeMaxCard
import AFTD.Kb.Tcs.TwoFourEventualThreshold

/-!
# op_491_threshold_ge_two_q_plus_one_of_ne

Topic: information   Node: 4c022cc9f6b7

Provenance: helper lemma. arXiv:2610.30613 Remark 6.1

Assuming the stabilization threshold set is nonempty, if $A_q(2q, \\{2,4\\}) \\ne 1 + \\binom{2q}{2}$, then the eventual length threshold satisfies $2q + 1 \\le N_*(q)$.
-/

/-- If A_q(2q, {2,4}) ≠ 1 + C(2q, 2), then 2q + 1 ≤ N_*(q). -/
theorem op_491_threshold_ge_two_q_plus_one_of_ne (q : ℕ) (h_nonempty : ∃ N, ∀ m ≥ N, two_four_code_max_card q m = 1 + Nat.choose m 2) (hne : two_four_code_max_card q (2 * q) ≠ 1 + Nat.choose (2 * q) 2) : 2 * q + 1 ≤ two_four_eventual_threshold q := by first | exact op_491_threshold_gt_of_ne | (apply op_491_threshold_gt_of_ne <;> assumption) | (apply op_491_threshold_gt_of_ne <;> simp_all) | simpa using op_491_threshold_gt_of_ne | (simp only [two_four_code_max_card, two_four_eventual_threshold] at *; first | exact op_491_threshold_gt_of_ne | (apply op_491_threshold_gt_of_ne <;> assumption) | (apply op_491_threshold_gt_of_ne <;> simp_all) | simpa using op_491_threshold_gt_of_ne)
