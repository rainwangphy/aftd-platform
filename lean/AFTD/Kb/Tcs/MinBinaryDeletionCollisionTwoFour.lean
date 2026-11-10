import AFTD.Prelude
import AFTD.Kb.Tcs.MinBinaryDeletionCollision

/-!
# min_binary_deletion_collision_two_four

Topic: information   Node: dbf7556adb30

Provenance: helper lemma. arXiv:2611.01064: Maximal input entropy for binary two-deletion and two-insertion channels

The minimum two-deletion collision sum min_binary_deletion_collision 2 4 equals 10.
-/

/-- The minimum two-deletion collision sum for binary words of length 4 is 10. -/
theorem min_binary_deletion_collision_two_four : min_binary_deletion_collision 2 4 = 10 := rfl
