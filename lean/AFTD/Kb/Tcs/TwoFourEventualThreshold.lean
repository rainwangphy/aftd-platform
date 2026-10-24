import AFTD.Prelude
import AFTD.Kb.Tcs.TwoFourCodeMaxCard

/-!
# two_four_eventual_threshold

Topic: information   Node: e4a7d67ee6da

Provenance: formalization of a published result. Source: arXiv:2610.30613, Section 1, after eq. (3)

For an integer $q$, the eventual length threshold $N_*(q)$ is the infimum of all integers $N$ such that $A_q(n, \{2,4\}) = 1 + \binom{n}{2}$ for all integers $n \ge N$.
-/

/-- N_*(q): the smallest integer N such that A_q(n, {2,4}) = 1 + Nat.choose n 2 for all n >= N. -/
noncomputable def two_four_eventual_threshold (q : ℕ) : ℕ := sInf { N : ℕ | ∀ n ≥ N, two_four_code_max_card q n = 1 + Nat.choose n 2 }
