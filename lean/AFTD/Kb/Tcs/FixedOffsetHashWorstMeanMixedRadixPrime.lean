import AFTD.Prelude
import AFTD.Kb.Tcs.MixedRadixOffset
import AFTD.Kb.Tcs.MixedRadixOffsetPrime
import AFTD.Kb.Tcs.LinearProbeOffset
import AFTD.Kb.Tcs.HashProbeExpectedCost

/-!
# fixed_offset_hash_worst_mean_mixed_radix_prime

Topic: data_structures   Node: 292f6cd6e876

Provenance: helper lemma. arXiv:2610.31363

For any prime p, any bijective offset sequence r : Fin p → ZMod p, and any load t < p, if linear probing achieves expected probe cost at least that of r, then there exists an ordering P of the prime factors of p such that the expected probe cost under r is at most that under the mixed-radix offset for P.
-/

/-- For prime table size, OP-809 reduces to linear probing maximizing the expected probe cost. -/
theorem fixed_offset_hash_worst_mean_mixed_radix_prime
    (p : ℕ) [Fact (Nat.Prime p)]
    (r : Fin p → ZMod p) (hr_bij : Function.Bijective r)
    (t : ℕ) (ht : t < p)
    (h_lin : hash_probe_expected_cost p r t ≤ hash_probe_expected_cost p (linear_probe_offset p) t) :
    ∃ P : List ℕ, P.Perm (Nat.primeFactorsList p) ∧
      hash_probe_expected_cost p r t ≤ hash_probe_expected_cost p (mixed_radix_offset p P) t := by
  use [p]
  constructor
  · rw [Nat.primeFactorsList_prime Fact.out]
  · have h_eq : mixed_radix_offset p [p] = linear_probe_offset p := by
      ext j
      exact mixed_radix_offset_prime p j
    rw [h_eq]
    exact h_lin
