import AFTD.Prelude
import AFTD.Kb.Tcs.StringOverlapMerge

/-!
# string_overlap_merge_sanity

Topic: approximation   Node: d7fa0e6b3326

Provenance: helper lemma. Sanity check of string_overlap_merge (arXiv:2611.16573)

⟨123, 234⟩ = 1234.
-/

theorem string_overlap_merge_sanity :
    string_overlap_merge [1, 2, 3] [2, 3, 4] = [1, 2, 3, 4] := by decide
