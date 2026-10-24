import AFTD.Prelude
import AFTD.Kb.Tcs.TwoFourCodeMaxCard
import AFTD.Kb.Tcs.TwoFourEventualThreshold

/-!
# op_491_threshold_gt_of_ne

Topic: information   Node: c81019c49f29

Provenance: helper lemma. arXiv:2610.30613 Section 6

Assuming the stabilization threshold set is nonempty, if $A_q(n, \\{2,4\\}) \\ne 1 + \\binom{n}{2}$ for some length $n$, then $n$ is strictly less than the eventual length threshold $N_*(q)$.
-/

/-- If A_q(n, {2,4}) ≠ 1 + choose n 2 and the threshold set is nonempty, then n < N_*(q). -/
theorem op_491_threshold_gt_of_ne (q n : ℕ)
    (h_nonempty : ∃ N, ∀ m ≥ N, two_four_code_max_card q m = 1 + Nat.choose m 2)
    (hne : two_four_code_max_card q n ≠ 1 + Nat.choose n 2) :
    n < two_four_eventual_threshold q := by
  by_contra! hle
  have h_mem : two_four_eventual_threshold q ∈ { N : ℕ | ∀ m ≥ N, two_four_code_max_card q m = 1 + Nat.choose m 2 } :=
    Nat.sInf_mem h_nonempty
  exact hne (h_mem n hle)
