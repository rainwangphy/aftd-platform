import AFTD.Prelude
import AFTD.Kb.Tcs.MinTwoInsertionCollision
import AFTD.Kb.Tcs.TwoInsertionCollisionDefectEnvelope
import AFTD.Kb.Tcs.TwoInsertionCollisionDefectEnvelopeFive

/-!
# op_1003_two_insertion_collision_defect_envelope_five

Topic: information   Node: 3c0deb06fd48

Provenance: helper lemma. arXiv:2611.01064 Maximal input entropy for binary two-deletion and two-insertion channels

The minimum two-insertion collision sum min_two_insertion_collision at length 5 equals two_insertion_collision_defect_envelope 5.
-/

/-- At received length five, the minimum two-insertion collision sum equals the balanced defect envelope value 20. -/
theorem op_1003_two_insertion_collision_defect_envelope_five :
    min_two_insertion_collision 5 = two_insertion_collision_defect_envelope 5 := rfl
