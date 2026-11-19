import AFTD.Prelude
import AFTD.Kb.Tcs.BpeFullMerge
import AFTD.Kb.Tcs.BpeMaxPairCount
import AFTD.Kb.Tcs.BpeGreedyStep
import AFTD.Kb.Tcs.BpePartialStep
import AFTD.Kb.Tcs.BpePartialMerge
import AFTD.Kb.Tcs.BpeSteps
import AFTD.Kb.Tcs.BpeWorstCaseRatioThreeUpperBound
import AFTD.Kb.Tcs.BpePairCount

/-!
# op1287_bpe_six_block_unit_comparator

Topic: algorithms   Node: 9ee3ebc78231

Provenance: helper lemma. OP-1287 tight comparator illustration, the unit case of arXiv:2611.08671v1, Section 3; experiment 31921. This asserts a comparator lower bound and equality with the proposed right side, not an upper bound on the optimum.

For the displayed six-block string with distinct separators, merging 1,2 is a greedy first step of utility 2, the next maximum pair count is 1, and the displayed five partial steps achieve utility 9, equal to twice the first greedy utility plus five times the next maximum count.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem op1287_bpe_six_block_unit_comparator :
    let s : List ℕ := [0,1,2,3,6, 0,1,7, 2,3,8, 4,1,2,5,9, 4,1,10, 2,5,11]
    let g := bpe_full_merge 1 2 12 s
    let u := bpe_full_merge 2 5 16 (bpe_full_merge 4 1 15
      (bpe_full_merge 12 13 14 (bpe_full_merge 2 3 13 (bpe_full_merge 0 1 12 s))))
    bpe_max_pair_count s = 2 ∧ bpe_greedy_step s g ∧ bpe_max_pair_count g = 1 ∧
      bpe_steps bpe_partial_step 5 s u ∧ s.length - u.length = 9 ∧
      2 * (s.length - g.length) + 5 * bpe_max_pair_count g = 9 := by
  dsimp only
  refine ⟨by decide, ?_, by decide, ?_, by decide, by decide⟩
  · right
    exact ⟨1, 2, 12, by decide, by decide, by decide, rfl⟩
  · refine ⟨_, Or.inr ⟨0, 1, 12, by decide, bpe3ub_partial_of_full 0 1 12 _⟩,
      _, Or.inr ⟨2, 3, 13, by decide, bpe3ub_partial_of_full 2 3 13 _⟩,
      _, Or.inr ⟨12, 13, 14, by decide, bpe3ub_partial_of_full 12 13 14 _⟩,
      _, Or.inr ⟨4, 1, 15, by decide, bpe3ub_partial_of_full 4 1 15 _⟩,
      _, Or.inr ⟨2, 5, 16, by decide, bpe3ub_partial_of_full 2 5 16 _⟩, rfl⟩
