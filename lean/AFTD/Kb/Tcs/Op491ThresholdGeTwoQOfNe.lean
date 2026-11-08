import AFTD.Prelude
import AFTD.Kb.Tcs.Op491ThresholdGtOfNe
import AFTD.Kb.Tcs.TwoFourCodeMaxCard
import AFTD.Kb.Tcs.TwoFourEventualThreshold

/-!
# op_491_threshold_ge_two_q_of_ne

Topic: information   Node: 9355988d736f

Provenance: helper lemma. arXiv:2610.30613 Remark 6.1

Assuming the stabilization threshold set is nonempty, if $A_q(2q - 1, \\{2,4\\}) \\ne 1 + \\binom{2q - 1}{2}$, then the eventual length threshold satisfies $2q \\le N_*(q)$.
-/

/-- If A_q(2q-1, {2,4}) ≠ 1 + C(2q-1, 2), then 2q ≤ N_*(q). -/
theorem op_491_threshold_ge_two_q_of_ne (q : ℕ) (h_nonempty : ∃ N, ∀ m ≥ N, two_four_code_max_card q m = 1 + Nat.choose m 2) (hne : two_four_code_max_card q (2 * q - 1) ≠ 1 + Nat.choose (2 * q - 1) 2) : 2 * q ≤ two_four_eventual_threshold q := by
  have h := op_491_threshold_gt_of_ne q (2 * q - 1) h_nonempty hne
  omega
