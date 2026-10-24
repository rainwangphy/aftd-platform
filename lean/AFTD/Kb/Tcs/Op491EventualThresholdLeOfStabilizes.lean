import AFTD.Prelude
import AFTD.Kb.Tcs.TwoFourCodeMaxCard
import AFTD.Kb.Tcs.TwoFourEventualThreshold

/-!
# op_491_eventual_threshold_le_of_stabilizes

Topic: information   Node: 92101fb772ca

Provenance: helper lemma. arXiv:2610.30613 Section 1

If a natural number $N$ has the property that $A_q(n, \\{2,4\\}) = 1 + \\binom{n}{2}$ for all integers $n \\ge N$, then the eventual length threshold $N_*(q)$ is at most $N$.
-/

/-- If A_q(n, {2,4}) stabilizes at 1 + choose n 2 from length N onwards, the threshold N_*(q) is at most N. -/
theorem op_491_eventual_threshold_le_of_stabilizes (q N : ℕ)
    (hN : ∀ n ≥ N, two_four_code_max_card q n = 1 + Nat.choose n 2) :
    two_four_eventual_threshold q ≤ N := by
  unfold two_four_eventual_threshold
  exact Nat.sInf_le hN
