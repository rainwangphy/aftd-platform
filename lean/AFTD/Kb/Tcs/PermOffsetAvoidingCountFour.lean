import AFTD.Prelude
import AFTD.Kb.Tcs.PermOffsetAvoidingCount

/-!
# perm_offset_avoiding_count_four

Topic: combinatorics   Node: d15d37758ac0

Provenance: helper lemma. sanity check for perm_offset_avoiding_count (PR-300)

Sanity check: U(4) = 2, and there are 4 permutations of 4 elements avoiding the offsets -1 and 1.
-/

theorem perm_offset_avoiding_count_four :
    perm_offset_avoiding_count 4 {-1, 0} = 2 ∧ perm_offset_avoiding_count 4 {-1, 1} = 4 := by decide
