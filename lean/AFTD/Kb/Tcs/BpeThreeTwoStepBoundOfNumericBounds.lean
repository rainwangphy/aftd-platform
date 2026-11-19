import AFTD.Prelude
import AFTD.Kb.Tcs.BpeGreedyStepUtilityEqMax
import AFTD.Kb.Tcs.BpeGreedyStepLengthLe
import AFTD.Kb.Tcs.BpeOptimalUtility
import AFTD.Kb.Tcs.BpeMaxPairCount
import AFTD.Kb.Tcs.BpeGreedyStep

/-!
# bpe_three_two_step_bound_of_numeric_bounds

Topic: algorithms   Node: 78ac7e8f31b7

Provenance: helper lemma. Arithmetic reduction for the budget-three case of OP-1287.

For two greedy steps s to u to v, if the optimal three-merge utility is at most the two-merge optimum plus the initial maximum pair count, and the two-merge optimum is at most the initial maximum plus twice the maximum after the first greedy step, then the three-merge optimum is at most twice the total two-step greedy saving.
-/

theorem bpe_three_two_step_bound_of_numeric_bounds
    (s u v : List ℕ)
    (h1 : bpe_greedy_step s u) (h2 : bpe_greedy_step u v)
    (hgrowth : bpe_optimal_utility s 3 ≤ bpe_optimal_utility s 2 + bpe_max_pair_count s)
    (htwo : bpe_optimal_utility s 2 ≤ bpe_max_pair_count s + 2 * bpe_max_pair_count u) :
    bpe_optimal_utility s 3 ≤ 2 * (s.length - v.length) := by
  have hlen1 := bpe_greedy_step_length_le s u h1
  have hlen2 := bpe_greedy_step_length_le u v h2
  have hu1 := bpe_greedy_step_utility_eq_max s u h1
  have hu2 := bpe_greedy_step_utility_eq_max u v h2
  omega
