import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeTailProb
import AFTD.Kb.Tcs.HashOccupiedSlotsCard
import AFTD.Kb.Tcs.HashOccupiedSlots
import AFTD.Kb.Tcs.HashProbeTailCount

/-!
# hash_probe_tail_prob_one

Topic: data_structures   Node: bbf80d12d72f

Provenance: helper lemma. step towards unit_first_fixed_offset_mean_probe_maximum

For any table size n ≥ 2 with [NeZero n], any bijective offset sequence r with r 0 = 0, and any load t ≤ n, the 1st tail probability hash_probe_tail_prob n r t 1 is identically equal to (t : ℝ) / (n : ℝ).
-/

/-- For any bijective offset sequence with r 0 = 0 and load t ≤ n, the k=1 probe tail probability is t / n. -/
theorem hash_probe_tail_prob_one (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (r : Fin n → ZMod n) (hr : Function.Bijective r) (hr0 : r 0 = 0)
    (t : ℕ) (ht : t ≤ n) :
    hash_probe_tail_prob n r t 1 = (t : ℝ) / (n : ℝ) := by
  have h_filter_eq : ∀ (A : Fin t → ZMod n),
      (Finset.filter (fun b : ZMod n => ∀ (j : Fin n), (j : ℕ) < 1 → b + r j ∈ hash_occupied_slots n r (List.ofFn A)) Finset.univ)
      = hash_occupied_slots n r (List.ofFn A) := by
    intro A
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have h0 : ((0 : Fin n) : ℕ) < 1 := by simp
      have := h 0 h0
      rwa [hr0, add_zero] at this
    · intro h j hj
      have hj0 : j = 0 := by
        ext
        simp only [Fin.val_zero]
        omega
      subst hj0
      rwa [hr0, add_zero]
  have h_count : hash_probe_tail_count n r t 1 = n ^ t * t := by
    unfold hash_probe_tail_count
    rw [Finset.card_filter]
    rw [Fintype.sum_prod_type]
    have h_inner : ∀ A : Fin t → ZMod n,
        (∑ y : ZMod n, if (∀ (j : Fin n), (j : ℕ) < 1 → y + r j ∈ hash_occupied_slots n r (List.ofFn A)) then 1 else 0) = t := by
      intro A
      rw [← Finset.card_filter]
      rw [h_filter_eq A]
      have hlen : (List.ofFn A).length ≤ n := by
        simp only [List.length_ofFn]
        exact ht
      rw [hash_occupied_slots_card n r hr (List.ofFn A) hlen, List.length_ofFn]
    simp_rw [h_inner]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  unfold hash_probe_tail_prob
  rw [h_count]
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hpow : (n : ℝ) ^ (t + 1) = (n : ℝ) ^ t * (n : ℝ) := by rw [pow_succ]
  push_cast
  rw [hpow]
  have hnt : (n : ℝ) ^ t ≠ 0 := pow_ne_zero t hn0
  rw [mul_div_mul_left _ _ hnt]
