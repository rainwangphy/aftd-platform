import AFTD.Prelude
import AFTD.Kb.Tcs.GreedyDistinctDiffNext

/-!
# greedy_distinct_diff_history

Topic: combinatorics   Node: d5660481db47

Provenance: formalization of a published result. Source: arXiv:2610.15860 (A note on the Slater–Vélez permutation), first paragraph (the greedy rule, here with arbitrary starting terms).

The first n + 2 terms of the greedy sequence started at a₁, a₂, most recent first.
-/

/-- The first `n + 2` terms of the greedy sequence started at `a₁, a₂`, most recent first. -/
noncomputable def greedy_distinct_diff_history (a₁ a₂ : ℕ) : ℕ → List ℕ
  | 0 => [a₂, a₁]
  | n + 1 => greedy_distinct_diff_next (greedy_distinct_diff_history a₁ a₂ n) ::
      greedy_distinct_diff_history a₁ a₂ n
