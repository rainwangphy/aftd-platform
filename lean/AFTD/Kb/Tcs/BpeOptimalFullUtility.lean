import AFTD.Prelude
import AFTD.Kb.Tcs.BpeFullStep
import AFTD.Kb.Tcs.BpeSteps

/-!
# bpe_optimal_full_utility

Topic: algorithms   Node: eca2907d88b1

Provenance: formalization of a published result. Source: scout/2611-08671-greedy-byte-pair-encoding-achieves-at-least-0-361-of-the-op.md:290

The maximum total reduction in string length achieved by any k-step sequence of full Byte-Pair Encoding merges on s.
-/

/-- The supremum of length decrease achievable over all k-step full-merge sequences from string s. -/
noncomputable def bpe_optimal_full_utility (s : List ℕ) (k : ℕ) : ℕ := sSup {u : ℕ | ∃ t, bpe_steps bpe_full_step k s t ∧ u = s.length - t.length}
