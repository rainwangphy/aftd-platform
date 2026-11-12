import AFTD.Prelude
import AFTD.Kb.Tcs.BpeGreedyStepWith

/-!
# bpe_greedy_run

Topic: algorithms   Node: 8943ade5215e

Provenance: formalization of a published result. Source: Sennrich, Haddow, Birch, arXiv:1508.07909; Gage, C Users Journal 1994

The relation defining a k-step greedy Byte-Pair Encoding run on string s yielding string t: for k = 0 we have s = t, and for k + 1 there exists an intermediate string u such that bpe_greedy_run k s u and bpe_greedy_step_with (k + 2) u t.
-/

/-- A k-step greedy BPE run with fresh symbol IDs 2, 3, ..., k + 1. -/
def bpe_greedy_run : ℕ → List ℕ → List ℕ → Prop
| 0, s, t => s = t
| k + 1, s, t => ∃ u, bpe_greedy_run k s u ∧ bpe_greedy_step_with (k + 2) u t
