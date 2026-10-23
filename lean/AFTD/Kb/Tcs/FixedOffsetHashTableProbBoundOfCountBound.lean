import AFTD.Prelude
import AFTD.Kb.Tcs.HashCountFullyOccupied
import AFTD.Kb.Tcs.HashMaxOccupiedProb

/-!
# fixed_offset_hash_table_prob_bound_of_count_bound

Topic: data_structures   Node: 1240660c352c

Provenance: helper lemma. arXiv:2610.31363 Theorem 4.1

For any n : ℕ with NeZero n, r : Fin n → ZMod n, and k < t ≤ n, if (n : ℝ) * hash_count_fully_occupied n r S (t - 1) ≤ hash_count_fully_occupied n r S t * (1 - (k : ℝ) / t + (k : ℝ) / n) holds for all S : Finset (ZMod n) with S.card = k, then hash_max_occupied_prob n r k (t - 1) ≤ hash_max_occupied_prob n r k t * (1 - (k : ℝ) / t + (k : ℝ) / n).
-/

/-- Derivation of the recurrence on p_k(t) from the recurrence on F_S(t). -/
theorem fixed_offset_hash_table_prob_bound_of_count_bound
    (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (k t : ℕ)
    (hkt : k < t) (htn : t ≤ n)
    (hF : ∀ S : Finset (ZMod n), S.card = k →
      (n : ℝ) * hash_count_fully_occupied n r S (t - 1) ≤
        hash_count_fully_occupied n r S t * (1 - (k : ℝ) / t + (k : ℝ) / n)) :
    hash_max_occupied_prob n r k (t - 1) ≤
      hash_max_occupied_prob n r k t * (1 - (k : ℝ) / t + (k : ℝ) / n) := by
  have _ := htn
  dsimp only [hash_max_occupied_prob]
  set K : Finset (Finset (ZMod n)) := (Finset.univ : Finset (Finset (ZMod n))).filter (fun S => S.card = k)
  set c : ℝ := 1 - (k : ℝ) / t + (k : ℝ) / n
  set M1 : ℕ := K.sup (fun S => hash_count_fully_occupied n r S (t - 1))
  set M2 : ℕ := K.sup (fun S => hash_count_fully_occupied n r S t)
  have ht_pos : 0 < t := by omega
  have hc_nonneg : 0 ≤ c := by
    have ht_pos_real : (0 : ℝ) < (t : ℝ) := by positivity
    have hn_pos_real : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := NeZero.pos n
      positivity
    have hkt_real : (k : ℝ) < (t : ℝ) := by exact_mod_cast hkt
    have h1 : (k : ℝ) / t < 1 := by
      rw [div_lt_iff₀ ht_pos_real]
      linarith
    have h2 : 0 ≤ (k : ℝ) / n := by positivity
    change 0 ≤ 1 - (k : ℝ) / t + (k : ℝ) / n
    linarith
  have h_bound : (n : ℝ) * (M1 : ℝ) ≤ (M2 : ℝ) * c := by
    by_cases hK : K.Nonempty
    · obtain ⟨S_max, hS_max_mem, hS_max_eq⟩ := Finset.exists_mem_eq_sup K hK
        (fun S => hash_count_fully_occupied n r S (t - 1))
      have hS_card : S_max.card = k := (Finset.mem_filter.mp hS_max_mem).2
      have hF_max := hF S_max hS_card
      have hS_le : hash_count_fully_occupied n r S_max t ≤ M2 :=
        Finset.le_sup (f := fun S => hash_count_fully_occupied n r S t) hS_max_mem
      have hS_le_real : (hash_count_fully_occupied n r S_max t : ℝ) ≤ (M2 : ℝ) := by
        exact_mod_cast hS_le
      have h_mul_le : (hash_count_fully_occupied n r S_max t : ℝ) * c ≤ (M2 : ℝ) * c :=
        mul_le_mul_of_nonneg_right hS_le_real hc_nonneg
      have hM1_eq : M1 = hash_count_fully_occupied n r S_max (t - 1) := hS_max_eq
      rw [hM1_eq]
      exact le_trans hF_max h_mul_le
    · have hK_empty : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
      have hM1_zero : M1 = 0 := by
        change (K.sup (fun S => hash_count_fully_occupied n r S (t - 1))) = 0
        rw [hK_empty]
        rfl
      have hM2_zero : M2 = 0 := by
        change (K.sup (fun S => hash_count_fully_occupied n r S t)) = 0
        rw [hK_empty]
        rfl
      rw [hM1_zero, hM2_zero]
      simp only [Nat.cast_zero, mul_zero, zero_mul, le_refl]
  -- Now algebraic deduction
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := NeZero.pos n
    positivity
  have hnt_pos : (0 : ℝ) < (n : ℝ) ^ (t - 1) := by positivity
  have ht_eq : (n : ℝ) ^ t = (n : ℝ) ^ (t - 1) * (n : ℝ) := by
    have : t = (t - 1) + 1 := (Nat.sub_add_cancel (Nat.succ_le_of_lt ht_pos)).symm
    nth_rw 1 [this]
    rw [pow_succ]
  change (M1 : ℝ) / (n : ℝ) ^ (t - 1) ≤ ((M2 : ℝ) / (n : ℝ) ^ t) * c
  rw [ht_eq]
  have h_prod_pos : 0 < (n : ℝ) ^ (t - 1) * (n : ℝ) := mul_pos hnt_pos hn_pos
  have h_rw1 : (M1 : ℝ) / (n : ℝ) ^ (t - 1) = ((n : ℝ) * (M1 : ℝ)) / ((n : ℝ) ^ (t - 1) * (n : ℝ)) := by
    have h_cancel := (mul_div_mul_right (M1 : ℝ) ((n : ℝ) ^ (t - 1)) (ne_of_gt hn_pos)).symm
    rw [mul_comm (M1 : ℝ) (n : ℝ)] at h_cancel
    exact h_cancel
  have h_rw2 : ((M2 : ℝ) / ((n : ℝ) ^ (t - 1) * (n : ℝ))) * c = ((M2 : ℝ) * c) / ((n : ℝ) ^ (t - 1) * (n : ℝ)) := by
    ring
  rw [h_rw1, h_rw2]
  exact div_le_div_of_nonneg_right h_bound (le_of_lt h_prod_pos)
