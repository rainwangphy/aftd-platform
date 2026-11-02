import AFTD.Prelude
import AFTD.Kb.Tcs.LinearProbeOffset

/-!
# linear_probe_offset_zero

Topic: data_structures   Node: 27ebe1b7e376

Provenance: helper lemma. step towards unit_first_fixed_offset_mean_probe_maximum

For any table size n with [NeZero n], linear_probe_offset n 0 is 0.
-/

/-- The linear probe offset at index 0 is 0 in ZMod n. -/
theorem linear_probe_offset_zero (n : ℕ) [NeZero n] :
    linear_probe_offset n 0 = 0 := by
  unfold linear_probe_offset
  simp
