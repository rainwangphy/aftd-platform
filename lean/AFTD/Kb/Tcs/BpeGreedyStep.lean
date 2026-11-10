import AFTD.Prelude
import AFTD.Kb.Tcs.BpeMaxPairCount
import AFTD.Kb.Tcs.BpePairCount
import AFTD.Kb.Tcs.BpeFullMerge

/-!
# bpe_greedy_step

Topic: algorithms   Node: 829c8efb1a23

Provenance: helper lemma. Definitions for OP-1288, following arXiv:2611.08671, Section 2.

A greedy full-merge step selects any most frequent adjacent pair and a fresh symbol; a string without adjacent pairs remains unchanged.
-/

def bpe_greedy_step (s t : List ℕ) : Prop :=
  (bpe_max_pair_count s = 0 ∧ t = s) ∨
  ∃ a b z, 0 < bpe_max_pair_count s ∧ bpe_pair_count a b s = bpe_max_pair_count s ∧
    z ∉ s ∧ t = bpe_full_merge a b z s
