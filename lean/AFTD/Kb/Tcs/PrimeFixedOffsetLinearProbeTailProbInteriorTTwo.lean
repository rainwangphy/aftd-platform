import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeTailProb
import AFTD.Kb.Tcs.LinearProbeOffset
import AFTD.Kb.Tcs.LinearProbeOffsetBijective
import AFTD.Kb.Tcs.LinearProbeOffsetZero
import AFTD.Kb.Tcs.HashProbeTailCount
import AFTD.Kb.Tcs.PrimeFixedOffsetTailProbTwoTwo

/-!
# prime_fixed_offset_linear_probe_tail_prob_interior_t_two

Topic: data_structures   Node: 4d0da980a2ca

Provenance: helper lemma. step towards prime_fixed_offset_linear_probe_tail_prob_interior_le

At load t = 2 (where k = 2), the probe tail probability under any bijective offset r with r 0 = 0 is bounded by linear probing on any prime table size p > 2.
-/

/-- At load t = 2 (where k = 2), the probe tail probability under any bijective offset r with r 0 = 0 is bounded by (in fact equal to) linear probing on any prime table size p > 2. -/
theorem prime_fixed_offset_linear_probe_tail_prob_interior_t_two
    (p : ℕ) [Fact (Nat.Prime p)]
    (r : Fin p → ZMod p) (hr_bij : Function.Bijective r) (hr0 : r 0 = 0)
    (k : ℕ) (hk2 : 2 ≤ k) (hkt : k ≤ 2) (ht : 2 < p) :
    hash_probe_tail_prob p r 2 k ≤ hash_probe_tail_prob p (linear_probe_offset p) 2 k := by
  have hk : k = 2 := by omega
  subst hk
  have h1 := prime_fixed_offset_tail_prob_two_two p ht r hr_bij hr0
  have h2 := prime_fixed_offset_tail_prob_two_two p ht (linear_probe_offset p)
    (linear_probe_offset_bijective p) (linear_probe_offset_zero p)
  rw [h1, h2]
