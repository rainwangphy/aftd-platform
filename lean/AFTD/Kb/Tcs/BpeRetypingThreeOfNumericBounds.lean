import AFTD.Prelude
import AFTD.Kb.Tcs.BpeThreeTwoStepBoundOfNumericBounds
import AFTD.Kb.Tcs.BpeSteps
import AFTD.Kb.Tcs.BpeGreedyStepUtilityEqMax
import AFTD.Kb.Tcs.BpeGreedyStepLengthLe
import AFTD.Kb.Tcs.BpeOptimalUtility
import AFTD.Kb.Tcs.BpeMaxPairCount
import AFTD.Kb.Tcs.BpeGreedyStep

/-!
# bpe_retyping_three_of_numeric_bounds

Topic: algorithms   Node: b65c2dc27087

Provenance: helper lemma. Arithmetic reduction for the budget-three case of OP-1287.

If the three-merge optimum is at most three initial maximum pair counts, it is at most the two-merge optimum plus one initial maximum, and the two-merge optimum is bounded by the initial maximum plus twice the maximum after any first greedy step, then for every greedy prefix of length i less than three its optimal three-merge utility is at most twice the prefix saving plus three times the maximum pair count at the resulting string.
-/

theorem bpe_retyping_three_of_numeric_bounds
    (s t : List ℕ) (i : ℕ) (hi : i < 3)
    (hg : bpe_steps bpe_greedy_step i s t)
    (hinit : bpe_optimal_utility s 3 ≤ 3 * bpe_max_pair_count s)
    (hgrowth : bpe_optimal_utility s 3 ≤ bpe_optimal_utility s 2 + bpe_max_pair_count s)
    (htwo : ∀ u, bpe_greedy_step s u →
      bpe_optimal_utility s 2 ≤ bpe_max_pair_count s + 2 * bpe_max_pair_count u) :
    bpe_optimal_utility s 3 ≤ 2 * (s.length - t.length) + 3 * bpe_max_pair_count t := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · simp only [bpe_steps] at hg
    subst t
    simpa using hinit
  · rcases hg with ⟨u, hu, heq⟩
    simp only [bpe_steps] at heq
    subst t
    have hlen := bpe_greedy_step_length_le s u hu
    have hval := bpe_greedy_step_utility_eq_max s u hu
    have hb := htwo u hu
    omega
  · rcases hg with ⟨u, hu, v, hv, heq⟩
    simp only [bpe_steps] at heq
    subst t
    have hb := bpe_three_two_step_bound_of_numeric_bounds s u v hu hv hgrowth (htwo u hu)
    omega
