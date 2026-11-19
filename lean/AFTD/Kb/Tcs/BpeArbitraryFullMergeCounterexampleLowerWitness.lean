import AFTD.Prelude
import AFTD.Kb.Tcs.BpeFullStep
import AFTD.Kb.Tcs.BpeFullMerge
import AFTD.Kb.Tcs.BpeSteps
import AFTD.Kb.Tcs.BpePartialStep
import AFTD.Kb.Tcs.BpePartialMerge
import AFTD.Kb.Tcs.BpeWorstCaseRatioThreeUpperBound

/-!
# bpe_arbitrary_full_merge_counterexample_lower_witness

Topic: algorithms   Node: 4c30bb3f8a2b

Provenance: helper lemma. Explicit comparator for experiment 34428, related to OP-1287.

The proposed arbitrary-full-merge stability counterexample has a full merge saving one and a three-step comparator saving eight. This does not assert an upper bound on the optimum after the merge.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem bpe_arbitrary_full_merge_counterexample_lower_witness : let s : List ℕ := [0,0,0,0,1,0,0,0,0,1]
    let t : List ℕ := [0,0,0,0,2,0,0,0,1]
    let v : List ℕ := [4,4]
    bpe_full_step s t ∧ s.length - t.length = 1 ∧
      bpe_steps bpe_partial_step 3 s v ∧ s.length - v.length = 8 := by
  dsimp only
  refine ⟨Or.inr ⟨1,0,2, by decide, rfl⟩, by decide, ?_, by decide⟩
  refine ⟨_, Or.inr ⟨0,0,2, by decide, bpe3ub_partial_of_full 0 0 2 _⟩,
    _, Or.inr ⟨2,2,3, by decide, bpe3ub_partial_of_full 2 2 3 _⟩,
    _, Or.inr ⟨3,1,4, by decide, bpe3ub_partial_of_full 3 1 4 _⟩, ?_⟩
  rfl
