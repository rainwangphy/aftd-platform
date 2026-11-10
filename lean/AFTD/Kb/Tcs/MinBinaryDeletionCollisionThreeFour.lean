import AFTD.Prelude
import AFTD.Kb.Tcs.MinBinaryDeletionCollision

/-!
# min_binary_deletion_collision_three_four

Topic: information   Node: 0d3825a0419b

Provenance: helper lemma. arXiv:2611.01064: Maximal input entropy for binary two-deletion and two-insertion channels

The minimum three-deletion collision sum min_binary_deletion_collision 3 4 equals 8.
-/

/-- The minimum three-deletion collision sum for binary words of length 4 is 8. -/
theorem min_binary_deletion_collision_three_four : min_binary_deletion_collision 3 4 = 8 := rfl
