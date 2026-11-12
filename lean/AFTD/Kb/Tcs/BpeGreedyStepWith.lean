import AFTD.Prelude
import AFTD.Kb.Tcs.BpeMaxPairCount
import AFTD.Kb.Tcs.BpePairCount
import AFTD.Kb.Tcs.BpeFullMerge

/-!
# bpe_greedy_step_with

Topic: algorithms   Node: 07d4fabde81f

Provenance: formalization of a published result. Source: Sennrich, Haddow, Birch, arXiv:1508.07909; Gage, C Users Journal 1994

A greedy full Byte-Pair Encoding merge step with fresh symbol z: either no adjacent pair occurs with positive count in string s and t = s, or there exists an adjacent pair (a, b) achieving the maximal nonoverlapping pair count bpe_max_pair_count s and t is the result bpe_full_merge a b z s of replacing all nonoverlapping occurrences of (a, b) by z.
-/

/-- One greedy full BPE merge step replacing a maximal pair with fresh symbol z, or leaving the string unchanged if no pair occurs. -/
def bpe_greedy_step_with (z : ℕ) (s t : List ℕ) : Prop :=
  (bpe_max_pair_count s = 0 ∧ t = s) ∨
  ∃ a b, 0 < bpe_max_pair_count s ∧
    bpe_pair_count a b s = bpe_max_pair_count s ∧
    t = bpe_full_merge a b z s
