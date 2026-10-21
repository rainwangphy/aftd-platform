import AFTD.Prelude
import AFTD.Kb.Tcs.GreedyDistinctDiffSeq
import AFTD.Kb.Tcs.GreedyDistinctDiffSeqSurjective

/-!
# greedy_distinct_diff_seq_one_two_surjective

Topic: combinatorics   Node: c5294eedeb72

Provenance: formalization of a published result. Source: 'Permutations of the positive integers with restrictions on the sequence of differences' (Pacific J. Math. 71, 1977), main theorem, as cited in arXiv:2610.15860 (A note on the Slater–Vélez permutation); the special case a₁ = 1, a₂ = 2 of OP-203.

The greedy sequence with distinct consecutive differences started at 1, 2 takes every positive integer as a value.
-/

theorem greedy_distinct_diff_seq_one_two_surjective :
    ∀ v, 0 < v → ∃ n, greedy_distinct_diff_seq 1 2 n = v := by
  exact greedy_distinct_diff_seq_surjective 1 2 (by decide) (by decide) (by decide)
