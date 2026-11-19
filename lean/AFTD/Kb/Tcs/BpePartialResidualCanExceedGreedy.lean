import AFTD.Prelude
import AFTD.Kb.Tcs.BpeGreedyStep
import AFTD.Kb.Tcs.BpePartialStep
import AFTD.Kb.Tcs.BpePartialMerge
import AFTD.Kb.Tcs.BpeFullMerge
import AFTD.Kb.Tcs.BpeMaxPairCount
import AFTD.Kb.Tcs.BpePairCount

/-!
# bpe_partial_residual_can_exceed_greedy

Topic: algorithms   Node: 65c95f0ebf57

Provenance: helper lemma. Exact counterexample to a residual-count dominance route for OP-1287; experiment 34404.

There are a string, a greedy merge result, and a partial-merge result of the same input for which the partial result has a strictly larger maximum nonoverlapping pair count than the greedy result.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem bpe_partial_residual_can_exceed_greedy :
    ∃ s g p : List ℕ, bpe_greedy_step s g ∧ bpe_partial_step s p ∧
      bpe_max_pair_count g < bpe_max_pair_count p := by
  refine ⟨[0,0,1,0,0,0,1,0], bpe_full_merge 0 0 2 [0,0,1,0,0,0,1,0],
    [2,1,0,2,1,0], ?_, ?_, by decide⟩
  · right
    exact ⟨0,0,2, by decide, by decide, by decide, rfl⟩
  · right
    refine ⟨0,0,2, by decide, ?_⟩
    simp [bpe_partial_merge]
