import AFTD.Prelude
import AFTD.Kb.Tcs.MixedRadixOffset
import AFTD.Kb.Tcs.HashProbeExpectedCostZero
import AFTD.Kb.Tcs.HashProbeExpectedCost

/-!
# mixed_radix_offset_mean_probe_zero

Topic: data_structures   Node: 18f6b11e643b

Provenance: helper lemma. arXiv:2610.31363

For every table size n ≥ 2, every probe sequence r : Fin n → ZMod n, and every factor list P, the expected probe cost into an empty table (t = 0) under r is at most the expected probe cost under the mixed-radix offset sequence for P.
-/

/-- At load t = 0, any offset sequence achieves expected cost at most the mixed-radix offset cost. -/
theorem mixed_radix_offset_mean_probe_zero
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (r : Fin n → ZMod n) (P : List ℕ) :
    hash_probe_expected_cost n r 0 ≤ hash_probe_expected_cost n (mixed_radix_offset n P) 0 := by
  rw [hash_probe_expected_cost_zero, hash_probe_expected_cost_zero]
