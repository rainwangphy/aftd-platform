import AFTD.Prelude
import AFTD.Kb.Tcs.BpeFullMerge
import AFTD.Kb.Tcs.BpeMaxPairCount
import AFTD.Kb.Tcs.BpeGreedyStep
import AFTD.Kb.Tcs.BpePartialStep
import AFTD.Kb.Tcs.BpePartialMerge
import AFTD.Kb.Tcs.BpeSteps
import AFTD.Kb.Tcs.BpePairCount
import AFTD.Kb.Tcs.BpeWorstCaseRatioThreeUpperBound

/-!
# bpe_refund_pair_slot_obstruction

Topic: algorithms   Node: 5e42bd15e8e5

Provenance: helper lemma. Exact pair-count witness against a naive independent refund-slot bound for OP-1287; experiment 34410.

For the displayed string, a greedy self-pair merge and a two-step partial comparator exist; after the greedy step the two displayed pair types each occur once while the maximum count is one, and the weighted sum of one full occurrence and one half occurrence exceeds that maximum. The partial comparator contains two copies of the retyped pair.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem bpe_refund_pair_slot_obstruction :
    let s : List ℕ := [0,0,1,2,0,0,0,1,3]
    let g := bpe_full_merge 0 0 4 s
    let p : List ℕ := [4,1,2,0,4,1,3]
    bpe_greedy_step s g ∧ bpe_steps bpe_partial_step 2 s [5,2,0,5,3] ∧
      bpe_pair_count 0 1 g = 1 ∧ bpe_pair_count 4 1 g = 1 ∧
      bpe_max_pair_count g = 1 ∧ bpe_pair_count 4 1 p = 2 ∧
      2 * bpe_max_pair_count g < 2 * bpe_pair_count 0 1 g + bpe_pair_count 4 1 g := by
  dsimp only
  refine ⟨?_, ?_, by decide, by decide, by decide, by decide, by decide⟩
  · right
    exact ⟨0,0,4, by decide, by decide, by decide, rfl⟩
  · have hfirst : bpe_partial_merge 0 0 4 [0,0,1,2,0,0,0,1,3] [4,1,2,0,4,1,3] := by
      simp [bpe_partial_merge]
    refine ⟨[4,1,2,0,4,1,3], Or.inr ⟨0,0,4, by decide, hfirst⟩,
      _, Or.inr ⟨4,1,5, by decide, bpe3ub_partial_of_full 4 1 5 _⟩, ?_⟩
    rfl
