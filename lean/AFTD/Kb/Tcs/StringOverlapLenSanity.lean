import AFTD.Prelude
import AFTD.Kb.Tcs.StringOverlapLen

/-!
# string_overlap_len_sanity

Topic: approximation   Node: f3a37c3b7741

Provenance: helper lemma. Sanity check of string_overlap_len (arXiv:2611.16573)

ov(123,234) = 23, ov(11,11) = 1, ov(12,12) is empty.
-/

theorem string_overlap_len_sanity :
    string_overlap_len [1, 2, 3] [2, 3, 4] = 2 ∧ string_overlap_len [1, 1] [1, 1] = 1 ∧
      string_overlap_len [1, 2] [1, 2] = 0 := by decide
