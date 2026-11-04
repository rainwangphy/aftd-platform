import AFTD.Prelude
import AFTD.Kb.Tcs.TwoInsertionCollisionDefectEnvelope

/-!
# two_insertion_collision_defect_envelope_five

Topic: information   Node: d2eff58fd5ee

Provenance: helper lemma. arXiv:2611.01064 Maximal input entropy for binary two-deletion and two-insertion channels

The two-insertion collision defect envelope two_insertion_collision_defect_envelope at n = 5 equals 20.
-/

/-- The two-insertion collision defect envelope evaluates to 20 at length 5. -/
theorem two_insertion_collision_defect_envelope_five :
    two_insertion_collision_defect_envelope 5 = 20 := by
  rfl
