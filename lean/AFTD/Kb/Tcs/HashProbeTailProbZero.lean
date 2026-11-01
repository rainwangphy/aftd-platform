import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeTailProb
import AFTD.Kb.Tcs.HashProbeTailCount
import AFTD.Kb.Tcs.HashOccupiedSlots

/-!
# hash_probe_tail_prob_zero

Topic: data_structures   Node: 87508783b677

Provenance: helper lemma. step towards unit_first_fixed_offset_mean_probe_maximum

For any table size n with [NeZero n], offset sequence r : Fin n → ZMod n, and number of inserted keys t, the 0-th tail probability of probe cost hash_probe_tail_prob n r t 0 is 1.
-/

/-- For any table size n, offset sequence r, and load t, the 0-th tail probability of probe cost is 1. -/
theorem hash_probe_tail_prob_zero (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (t : ℕ) :
    hash_probe_tail_prob n r t 0 = 1 := by
  unfold hash_probe_tail_prob hash_probe_tail_count
  have h : (Finset.univ.filter (fun p : (Fin t → ZMod n) × ZMod n =>
      ∀ j : Fin n, (j : ℕ) < 0 → p.2 + r j ∈ hash_occupied_slots n r (List.ofFn p.1)))
      = Finset.univ := by
    rw [Finset.filter_true_of_mem]
    intro p _ j hj
    exact absurd hj (Nat.not_lt_zero _)
  rw [h, Finset.card_univ]
  have hcard : Fintype.card ((Fin t → ZMod n) × ZMod n) = n ^ t * n := by
    rw [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hcard]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hpow : (n : ℝ) ^ (t + 1) = (n : ℝ) ^ t * n := by rw [pow_succ]
  push_cast
  rw [hpow, div_self (mul_ne_zero (pow_ne_zero _ hn) hn)]
