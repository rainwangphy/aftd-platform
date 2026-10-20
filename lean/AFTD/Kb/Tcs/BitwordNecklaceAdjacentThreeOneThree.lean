import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordIsRotation
import AFTD.Kb.Tcs.BitwordNecklaceAdjacent

/-!
# bitword_necklace_adjacent_three_one_three

Topic: combinatorics   Node: 2cd1b12d89f1

Provenance: helper lemma. sanity check for bitword_is_rotation and bitword_necklace_adjacent (OP-392)

Sanity check: 100 is a rotation of 001, and the necklaces of 001 and 011 are adjacent in Q_3.
-/

theorem bitword_necklace_adjacent_three_one_three :
    bitword_is_rotation 3 1 4 ∧ bitword_necklace_adjacent 3 1 3 := ⟨⟨2, by decide, by decide⟩, ⟨0, by decide, 1, by decide, by decide⟩⟩
