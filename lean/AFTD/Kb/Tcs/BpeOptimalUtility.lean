import AFTD.Prelude
import AFTD.Kb.Tcs.BpeSteps
import AFTD.Kb.Tcs.BpePartialStep

/-!
# bpe_optimal_utility

Topic: algorithms   Node: d3368e983692

Provenance: helper lemma. Definitions for OP-1288, following arXiv:2611.08671, Section 2.

The supremum, over strings reachable in k partial-merge steps, of the reduction in length of the input string.
-/

noncomputable def bpe_optimal_utility (s : List ℕ) (k : ℕ) : ℕ :=
  sSup {u : ℕ | ∃ t, bpe_steps bpe_partial_step k s t ∧ u = s.length - t.length}
