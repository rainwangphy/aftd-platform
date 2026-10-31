import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_tight_class_inner_imp_one

Topic: combinatorics   Node: 08b01a67d93c

Provenance: helper lemma. Research thread RT-1, OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Helper for cycle_power_dyadic_alternating_paired_of_pairing.

For m ≥ 2 and a tight dyadic class b : ℕ → Bool at exponent m (class weight equal to class size) with b 1 = b (2^m - 2) and b (2i) = b (2i+1) whenever 1 ≤ i and i + 1 < 2^(m-1): every inner bit forces bit 1, i.e. if 0 < j < 2^m - 1 and b j = true then b 1 = true.
-/

theorem cycle_power_dyadic_tight_class_inner_imp_one (m : ℕ) (hm : 2 ≤ m) (b : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight m b =
      (Finset.range (2 ^ m)).sum (fun a => (b a).toNat))
    (h1 : b 1 = b (2 ^ m - 2))
    (hpr : ∀ i, 1 ≤ i → i + 1 < 2 ^ (m - 1) → b (2 * i) = b (2 * i + 1)) :
    ∀ j, 0 < j → j < 2 ^ m - 1 → b j = true → b 1 = true := by
  have hD : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hH : 2 ≤ 2 ^ (m - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have key : ∀ r, ∀ j, 0 < j → j < 2 ^ m - 1 → min j (2 ^ m - 1 - j) = r →
      b j = true → b 1 = true := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro j hj0 hj1 hr hb
      have hr0 : r ≠ 0 := by omega
      set s := Nat.log 2 r with hs
      have hs1 : 2 ^ s ≤ r := Nat.pow_log_le_self 2 hr0
      have hs2 : r < 2 ^ (s + 1) := Nat.lt_pow_succ_log_self (by norm_num) r
      have hsp : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
      have hrH : r < 2 ^ (m - 1) := by omega
      have hsm : s + 1 < m := by
        have : 2 ^ s < 2 ^ (m - 1) := lt_of_le_of_lt hs1 hrH
        have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp this
        omega
      have hsle : 2 ^ (s + 1) ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have P := cycle_power_dyadic_tight_class_parent m (s + 1) (by omega) hsm b htight
      simp only [Nat.add_sub_cancel] at P
      rcases Nat.lt_or_ge j (2 ^ (m - 1)) with hlow | hup
      · -- lower bit: j = r
        have hjr : j = r := by omega
        rw [← hjr] at hs1 hs2 hrH
        have hb' := (P j (by omega)).2 hs1 hb
        by_cases hj1' : j = 1
        · subst hj1'; exact hb
        by_cases hjt : j = 2 ^ (s + 1) - 1
        · -- use the pairing with j - 1, whose parent is 2^m - 2
          have hs0 : 1 ≤ s := by
            rcases Nat.eq_zero_or_pos s with h0 | h0
            · rw [h0] at hjt; norm_num at hjt; omega
            · exact h0
          have hs2' : 2 ≤ 2 ^ s := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs0
          have hp := hpr (2 ^ s - 1) (by omega) (by omega)
          rw [show 2 * (2 ^ s - 1) + 1 = j by omega] at hp
          rw [← hp] at hb
          have := (P (2 * (2 ^ s - 1)) (by omega)).2 (by omega) hb
          rw [show 2 * (2 ^ s - 1) + 2 ^ m - 2 ^ (s + 1) = 2 ^ m - 2 by omega] at this
          rw [h1]; exact this
        · exact ih (2 ^ (s + 1) - 1 - j) (by rw [← hjr]; omega) (j + 2 ^ m - 2 ^ (s + 1)) (by omega)
            (by omega) (by omega) hb'
      · -- upper bit: j = 2^m - 1 - r
        have hjr : j = 2 ^ m - 1 - r := by omega
        set a := 2 ^ (s + 1) - 1 - r with ha
        have hja : j = a + 2 ^ m - 2 ^ (s + 1) := by omega
        have hb' : b a = true := (P a (by omega)).1 (by omega) (by rw [← hja]; exact hb)
        by_cases ha0 : a = 0
        · by_cases hs0 : s = 0
          · -- j = 2^m - 2
            have h2s : 2 ^ s = 1 := by rw [hs0]; rfl
            have : j = 2 ^ m - 2 := by omega
            rw [h1, ← this]; exact hb
          · have hs2' : 2 ≤ 2 ^ s := by
              calc 2 = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
            have hp := hpr (2 ^ (m - 1) - 2 ^ s) (by omega) (by omega)
            rw [show 2 * (2 ^ (m - 1) - 2 ^ s) = j by omega] at hp
            rw [hp] at hb
            exact (P 1 (by omega)).1 (by omega) (by rw [show 1 + 2 ^ m - 2 ^ (s + 1) = j + 1 by omega]; exact hb)
        · exact ih a (by omega) a (by omega) (by omega) (by omega) hb'
  intro j hj0 hj1 hb
  exact key _ j hj0 hj1 rfl hb
