import AFTD.Prelude
import AFTD.Kb.Tcs.BpeSteps
import AFTD.Kb.Tcs.BpeGreedyStep
import AFTD.Kb.Tcs.BpeOptimalUtility

/-!
# bpe_worst_ratio

Topic: algorithms   Node: 68e7f0451337

Provenance: helper lemma. Definitions for OP-1288, following arXiv:2611.08671, Section 2.

For a merge budget k, the infimum of greedy length reduction divided by optimal partial-merge length reduction over finite natural-number strings and all greedy tie-breaking runs with positive optimum.
-/

noncomputable def bpe_worst_ratio (k : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ s t : List ℕ, bpe_steps bpe_greedy_step k s t ∧
    0 < bpe_optimal_utility s k ∧ r = ((s.length - t.length : ℕ) : ℝ) / bpe_optimal_utility s k}
