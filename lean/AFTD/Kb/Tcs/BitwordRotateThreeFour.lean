import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordRotate

/-!
# bitword_rotate_three_four

Topic: combinatorics   Node: 6314f8dbea01

Provenance: helper lemma. sanity check for bitword_rotate (OP-392)

Sanity check: rotating the 3-bit words 100 and 011 gives 001 and 110.
-/

theorem bitword_rotate_three_four : bitword_rotate 3 4 = 1 ∧ bitword_rotate 3 3 = 6 := by decide
