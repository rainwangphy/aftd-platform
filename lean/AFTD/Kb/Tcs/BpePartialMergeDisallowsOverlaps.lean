import AFTD.Prelude
import AFTD.Kb.Tcs.BpePartialMerge

/-!
# bpe_partial_merge_disallows_overlaps

Topic: algorithms   Node: 82aa13b70ccb

Provenance: helper lemma. Sanity check for the partial merge relation in OP-1288.

Two overlapping adjacent occurrences in a three-symbol run cannot both be merged.
-/

theorem bpe_partial_merge_disallows_overlaps : ¬ bpe_partial_merge 1 1 9 [1,1,1] [9,9] := by simp [bpe_partial_merge]
