import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeTailProb
import AFTD.Kb.Tcs.HashProbeExpectedCost
import AFTD.Kb.Tcs.LinearProbeOffset

/-!
# prime_fixed_offset_mean_le_of_tail_le

Topic: data_structures   Node: 5bc1f5ac6a1c

Provenance: helper lemma. arXiv:2610.31363: "A Sharp Analysis of Fixed Offset Hash Tables"

For any prime table size p, offset sequence r : Fin p → ZMod p, and load t, if every probe-cost tail probability under r is bounded by the corresponding tail probability under linear probing, then the expected probe cost under r is at most the expected probe cost under linear probing.
-/

/-- Pointwise tail probability dominance on a prime-size table implies expected probe cost dominance by linear probing. -/
theorem prime_fixed_offset_mean_le_of_tail_le
    (p : ℕ) [Fact (Nat.Prime p)] (r : Fin p → ZMod p) (t : ℕ)
    (h_tail : ∀ k : ℕ, hash_probe_tail_prob p r t k ≤ hash_probe_tail_prob p (linear_probe_offset p) t k) :
    hash_probe_expected_cost p r t ≤ hash_probe_expected_cost p (linear_probe_offset p) t := Finset.sum_le_sum fun k _ => h_tail k
