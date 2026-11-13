import AFTD.Prelude
import AFTD.Kb.Tcs.BpeGreedyStep
import AFTD.Kb.Tcs.BpeSteps

/-!
# bpe_min_greedy_utility

Topic: algorithms   Node: a71eb3799c8f

Provenance: formalization of a published result. Source: scout/2611-08671-greedy-byte-pair-encoding-achieves-at-least-0-361-of-the-op.md:59

The minimum total reduction in string length achieved by any k-step greedy Byte-Pair Encoding merge run on s under arbitrary tie-breaking.
-/

/-- The infimum of length decrease achievable by any k-step greedy Byte-Pair Encoding run from string s under arbitrary tie-breaking. -/
noncomputable def bpe_min_greedy_utility (s : List ℕ) (k : ℕ) : ℕ := sInf {u : ℕ | ∃ t, bpe_steps bpe_greedy_step k s t ∧ u = s.length - t.length}
