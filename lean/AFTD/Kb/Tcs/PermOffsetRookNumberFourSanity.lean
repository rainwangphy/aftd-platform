import AFTD.Prelude
import AFTD.Kb.Tcs.PermOffsetRookNumber

/-!
# perm_offset_rook_number_four_sanity

Topic: combinatorics   Node: aa6c890f0963

Provenance: helper lemma. arXiv:2610.23958 Section 6

For n = 4, the 4-th rook number for {-1, 0} is 2, and the 4-th rook number for {-1, 1} is 4: perm_offset_rook_number 4 {-1, 0} 4 = 2 and perm_offset_rook_number 4 {-1, 1} 4 = 4.
-/

/-- Sanity check: the 4-rook placements on 4x4 boards for {-1, 0} and {-1, 1} count 2 and 4 respectively. -/
theorem perm_offset_rook_number_four_sanity :
    perm_offset_rook_number 4 {-1, 0} 4 = 2 ∧ perm_offset_rook_number 4 {-1, 1} 4 = 4 := by
  decide
