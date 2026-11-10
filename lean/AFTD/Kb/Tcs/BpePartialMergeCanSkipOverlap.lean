import AFTD.Prelude
import AFTD.Kb.Tcs.BpePartialMerge

/-!
# bpe_partial_merge_can_skip_overlap

Topic: algorithms   Node: a8c17ae7799e

Provenance: helper lemma. Sanity check for the partial merge relation in OP-1288.

A partial merge of equal adjacent symbols may skip the first occurrence and merge the overlapping middle occurrence.
-/

theorem bpe_partial_merge_can_skip_overlap : bpe_partial_merge 1 1 9 [1,1,1,1] [1,9,1] := by simp [bpe_partial_merge]
