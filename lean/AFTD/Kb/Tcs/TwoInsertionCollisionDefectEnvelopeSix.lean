import AFTD.Prelude
import AFTD.Kb.Tcs.TwoInsertionCollisionDefectEnvelope

/-!
# two_insertion_collision_defect_envelope_six

Topic: information   Node: 53f5a84af47a

Provenance: helper lemma. arXiv:2611.01064 Maximal input entropy for binary two-deletion and two-insertion channels

The two-insertion collision defect envelope two_insertion_collision_defect_envelope at n = 6 equals 31.
-/

/-- The two-insertion collision defect envelope evaluates to 31 at length 6. -/
theorem two_insertion_collision_defect_envelope_six :
    two_insertion_collision_defect_envelope 6 = 31 := by
  decide
