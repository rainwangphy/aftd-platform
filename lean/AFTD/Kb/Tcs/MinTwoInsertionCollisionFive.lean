import AFTD.Prelude
import AFTD.Kb.Tcs.MinTwoInsertionCollision
import AFTD.Kb.Tcs.Op1003TwoInsertionCollisionDefectEnvelopeFive
import AFTD.Kb.Tcs.TwoInsertionCollisionDefectEnvelopeFive
import AFTD.Kb.Tcs.TwoInsertionCollisionDefectEnvelope

/-!
# min_two_insertion_collision_five

Topic: information   Node: 3466dcf759bc

Provenance: original. Related work: arXiv:2611.01064, Section 4.2

The minimum two-insertion collision sum min_two_insertion_collision 5 equals 20.
-/

/-- The minimum two-insertion collision sum for words of length 5 is 20. -/
theorem min_two_insertion_collision_five : min_two_insertion_collision 5 = 20 := op_1003_two_insertion_collision_defect_envelope_five.trans two_insertion_collision_defect_envelope_five
