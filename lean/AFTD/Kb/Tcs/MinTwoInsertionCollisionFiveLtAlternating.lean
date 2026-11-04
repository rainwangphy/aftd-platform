import AFTD.Prelude
import AFTD.Kb.Tcs.MinTwoInsertionCollision
import AFTD.Kb.Tcs.TwoInsertionCollision
import AFTD.Kb.Tcs.MinTwoInsertionCollisionFive
import AFTD.Kb.Tcs.AlternatingWord

/-!
# min_two_insertion_collision_five_lt_alternating

Topic: information   Node: 02c6ad53d4a5

Provenance: original. Related work: arXiv:2611.01064, Section 4.2

The minimum two-insertion collision sum min_two_insertion_collision 5 is strictly less than two_insertion_collision 3 (alternating_word 5 false).
-/

/-- The alternating word of length 5 is strictly suboptimal for two-insertion collisions. -/
theorem min_two_insertion_collision_five_lt_alternating :
    min_two_insertion_collision 5 < two_insertion_collision 3 (alternating_word 5 false) := by
  rw [min_two_insertion_collision_five]
  decide
