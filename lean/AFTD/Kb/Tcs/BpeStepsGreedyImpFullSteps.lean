import AFTD.Prelude
import AFTD.Kb.Tcs.BpeFullStep
import AFTD.Kb.Tcs.BpeGreedyStep
import AFTD.Kb.Tcs.BpeSteps
import AFTD.Kb.Tcs.BpePairCount
import AFTD.Kb.Tcs.BpeMaxPairCount
import AFTD.Kb.Tcs.BpeFullMerge

/-!
# bpe_steps_greedy_imp_full_steps

Topic: algorithms   Node: c24cad0962e3

Provenance: helper lemma. scout/2611-08671-greedy-byte-pair-encoding-achieves-at-least-0-361-of-the-op.md:59

Every string reachable by k steps of greedy Byte-Pair Encoding merges is also reachable by k general full-merge steps.
-/

/-- Every k-step greedy Byte-Pair Encoding run is a valid k-step full-merge sequence. -/
theorem bpe_steps_greedy_imp_full_steps (k : ℕ) (s t : List ℕ) (h : bpe_steps bpe_greedy_step k s t) : bpe_steps bpe_full_step k s t := by
  induction k generalizing s with
  | zero => exact h
  | succ k ih =>
    rcases h with ⟨u, hsu, hut⟩
    refine ⟨u, ?_, ih u hut⟩
    rcases hsu with ⟨-, rfl⟩ | ⟨a, b, z, -, -, hz, rfl⟩
    · left; rfl
    · right; exact ⟨a, b, z, hz, rfl⟩
