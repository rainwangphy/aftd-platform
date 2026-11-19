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
# op1287_bpe_two_greedy_three_comparator_sharp_witness

Topic: algorithms   Node: f489cf61cdd5

Provenance: helper lemma. Exact witness for the two-greedy versus three-comparator bound in OP-1287; experiments 34379 and 34380.

On the displayed eight-symbol string, a two-step greedy run saves three symbols and a three-step partial-merge run saves six symbols. The latter deliberately skips an overlapping occurrence in its first merge.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem op1287_bpe_two_greedy_three_comparator_sharp_witness :
    let s : List ℕ := [0,0,1,0,0,0,1,0]
    let g := bpe_full_merge 0 1 3 (bpe_full_merge 0 0 2 s)
    let v : List ℕ := [4,4]
    bpe_steps bpe_greedy_step 2 s g ∧ s.length - g.length = 3 ∧
      bpe_steps bpe_partial_step 3 s v ∧ s.length - v.length = 6 := by
  dsimp only
  refine ⟨?_, by decide, ?_, by decide⟩
  · refine ⟨_, Or.inr ⟨0,0,2, by decide, by decide, by decide, rfl⟩,
      _, Or.inr ⟨0,1,3, by decide, by decide, by decide, rfl⟩, rfl⟩
  · have hfirst : bpe_partial_merge 0 0 2 [0,0,1,0,0,0,1,0] [2,1,0,2,1,0] := by
      simp [bpe_partial_merge]
    refine ⟨[2,1,0,2,1,0], Or.inr ⟨0,0,2, by decide, hfirst⟩,
      _, Or.inr ⟨1,0,3, by decide, bpe3ub_partial_of_full 1 0 3 _⟩,
      _, Or.inr ⟨2,3,4, by decide, bpe3ub_partial_of_full 2 3 4 _⟩, ?_⟩
    rfl
