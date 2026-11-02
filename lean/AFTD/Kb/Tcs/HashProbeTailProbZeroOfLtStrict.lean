import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeTailProb
import AFTD.Kb.Tcs.HashProbeTailCountZeroOfLtStrict
import AFTD.Kb.Tcs.HashProbeTailCount

/-!
# hash_probe_tail_prob_zero_of_lt_strict

Topic: data_structures   Node: 03f8a27be528

Provenance: helper lemma. step towards prime_fixed_offset_linear_probe_stochastic_maximum

For any table size n with [NeZero n], any bijective offset sequence r, and load t < n, the probe tail probability is 0 whenever k > t.
-/

/-- For any table size n with [NeZero n], any bijective offset sequence r, and load t < n, the probe tail probability is 0 whenever k exceeds t. -/
theorem hash_probe_tail_prob_zero_of_lt_strict
    (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (hr : Function.Bijective r)
    (t k : ℕ) (ht : t < n) (hkt : t < k) :
    hash_probe_tail_prob n r t k = 0 := by
  dsimp [hash_probe_tail_prob]
  rw [hash_probe_tail_count_zero_of_lt_strict n r hr t k ht hkt]
  simp
