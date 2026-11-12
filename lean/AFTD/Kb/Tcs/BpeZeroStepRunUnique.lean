import AFTD.Prelude
import AFTD.Kb.Tcs.BpeGreedyRun

/-!
# bpe_zero_step_run_unique

Topic: algorithms   Node: a6cb86fa9da0

Provenance: helper lemma. knowledgebase, supporting OP-1533

A zero-step greedy Byte-Pair Encoding run from string s to string t holds if and only if s = t.
-/

/-- A zero-step greedy BPE run leaves the string identical. -/
theorem bpe_zero_step_run_unique (s t : List ℕ) :
    bpe_greedy_run 0 s t ↔ s = t := by
  simp [bpe_greedy_run]
