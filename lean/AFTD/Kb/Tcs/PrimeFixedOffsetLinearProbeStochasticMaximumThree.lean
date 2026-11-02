import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeTailProb
import AFTD.Kb.Tcs.LinearProbeOffset
import AFTD.Kb.Tcs.UnitFirstFixedOffsetMeanProbeMaximumThree
import AFTD.Kb.Tcs.HashOccupiedSlots
import AFTD.Kb.Tcs.HashProbeTailCount

/-!
# prime_fixed_offset_linear_probe_stochastic_maximum_three

Topic: data_structures   Node: 92fe30882e2f

Provenance: formalization of a published result. Source: arXiv:2610.31363: "A Sharp Analysis of Fixed Offset Hash Tables"

For a 3-slot hash table (p = 3), every bijective probe sequence r : Fin 3 → ZMod 3 with r 0 = 0, every load t < 3, and every integer k ≥ 0, the probability hash_probe_tail_prob 3 r t k of requiring strictly more than k probes is at most that under linear probing hash_probe_tail_prob 3 (linear_probe_offset 3) t k.
-/

lemma prime_fixed_offset_linear_probe_stochastic_maximum_three_count_ge
    (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (t : ℕ) (k : ℕ) (hk : n ≤ k) :
    hash_probe_tail_count n r t k = hash_probe_tail_count n r t n := by
  dsimp [hash_probe_tail_count]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h j hj
    exact h j (lt_of_lt_of_le j.is_lt hk)
  · intro h j hj
    exact h j j.is_lt

/-- For a 3-slot hash table, every bijective offset sequence with r 0 = 0 has probe-cost tail probabilities bounded by linear probing. -/
theorem prime_fixed_offset_linear_probe_stochastic_maximum_three
    (r : Fin 3 → ZMod 3) (hr_bij : Function.Bijective r) (hr0 : r 0 = 0)
    (t : ℕ) (ht : t < 3) (k : ℕ) :
    hash_probe_tail_prob 3 r t k ≤ hash_probe_tail_prob 3 (linear_probe_offset 3) t k := by
  rcases unit_first_fixed_offset_mean_probe_maximum_three_r_eq_or_eq r hr_bij.injective hr0 with rfl | rfl
  · exact le_rfl
  · dsimp [hash_probe_tail_prob]
    have h_count : hash_probe_tail_count 3 unit_first_fixed_offset_mean_probe_maximum_three_r_rev t k =
                   hash_probe_tail_count 3 (linear_probe_offset 3) t k := by
      by_cases hk : k < 4
      · exact unit_first_fixed_offset_mean_probe_maximum_three_r_rev_tail_count t ht k hk
      · have hk3 : 3 ≤ k := by omega
        rw [prime_fixed_offset_linear_probe_stochastic_maximum_three_count_ge 3 _ t k hk3]
        rw [prime_fixed_offset_linear_probe_stochastic_maximum_three_count_ge 3 (linear_probe_offset 3) t k hk3]
        exact unit_first_fixed_offset_mean_probe_maximum_three_r_rev_tail_count t ht 3 (by norm_num)
    rw [h_count]
