import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeExpectedCost
import AFTD.Kb.Tcs.LinearProbeOffset
import AFTD.Kb.Tcs.HashProbeExpectedCostZero

/-!
# unit_first_fixed_offset_mean_probe_eq_zero

Topic: data_structures   Node: 3bd5131ca119

Provenance: helper lemma. folklore

For every table size n ≥ 2 with [NeZero n] and every bijective probe sequence r : Fin n → ZMod n with r 0 = 0 and IsUnit (r 1), the expected insertion cost into an empty table (t = 0) under r equals that under linear probing, hash_probe_expected_cost n r 0 = hash_probe_expected_cost n (linear_probe_offset n) 0.
-/

/-- OP-805 holds with equality at load t = 0 for any probe sequence with r 0 = 0 and unit first offset. -/
theorem unit_first_fixed_offset_mean_probe_eq_zero
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (r : Fin n → ZMod n) (hr_bij : Function.Bijective r)
    (hr0 : r 0 = 0) (hr1 : IsUnit (r 1)) :
    hash_probe_expected_cost n r 0 = hash_probe_expected_cost n (linear_probe_offset n) 0 := by
  rw [hash_probe_expected_cost_zero, hash_probe_expected_cost_zero]
