import AFTD.Prelude
import AFTD.Kb.Tcs.GreedyDistinctDiffHistory

/-!
# greedy_distinct_diff_seq

Topic: combinatorics   Node: 2351079aa340

Provenance: formalization of a published result. Source: arXiv:2610.15860 (A note on the Slater–Vélez permutation), first paragraph (the greedy rule, here with arbitrary starting terms).

The greedy sequence with distinct consecutive differences started at a₁, a₂ (term 0 is a₁, term 1 is a₂; each later term is the least unused positive integer whose difference with the previous term is new).
-/

/-- The greedy sequence with distinct consecutive differences started at `a₁, a₂` (0-indexed). -/
noncomputable def greedy_distinct_diff_seq (a₁ a₂ : ℕ) : ℕ → ℕ
  | 0 => a₁
  | n + 1 => (greedy_distinct_diff_history a₁ a₂ n).headD 0
