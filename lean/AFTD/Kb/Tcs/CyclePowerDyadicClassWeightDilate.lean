import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerSumRangeDouble
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_class_weight_dilate

Topic: combinatorics   Node: 1945d9ddd720

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635, Section 3. These conditional class-system and pruning lemmas do not establish the unresolved graph covering bound. The earlier fixed-radius helpers handle radii eight and sixteen; this session works with arbitrary dyadic radii. No research advance is claimed.

Duplicating each membership bit of a dyadic class doubles its dyadic class weight, when the original radius is at least two.
-/

open Finset

theorem cycle_power_dyadic_class_weight_dilate
    (m : ℕ) (hm : 1 ≤ m) (c : ℕ → Bool) :
    cycle_power_dyadic_class_weight (m + 1) (fun j => c (j / 2)) =
      2 * cycle_power_dyadic_class_weight m c := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
  have hmk : m = k + 1 := by omega
  clear hk
  subst m
  have hpow (j : ℕ) : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; omega
  have hroot : (2 ^ (k + 1 + 1) - 1) / 2 = 2 ^ (k + 1) - 1 := by
    have hp := hpow (k + 1)
    have : 0 < 2 ^ (k + 1) := Nat.two_pow_pos _
    omega
  have hsum :
      (range (k + 1 + 1)).sum (fun j => if j = 0 then 0 else
        (range (2 ^ j)).sum (fun i =>
          (c (i / 2) && c ((i + 2 ^ (k + 1 + 1) - 2 ^ j) / 2)).toNat)) =
      2 * (c 0 && c (2 ^ (k + 1) - 1)).toNat +
      2 * (range (k + 1)).sum (fun j => if j = 0 then 0 else
        (range (2 ^ j)).sum (fun i => (c i && c (i + 2 ^ (k + 1) - 2 ^ j)).toNat)) := by
    have hn : k + 1 + 1 = (k + 1) + 1 := by omega
    rw [hn, sum_range_succ']
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_zero]
    have hterm : ∀ j < k + 1,
        (range (2 ^ (j + 1))).sum (fun i =>
          (c (i / 2) && c ((i + 2 ^ (k + 1 + 1) - 2 ^ (j + 1)) / 2)).toNat) =
        2 * (range (2 ^ j)).sum (fun i =>
          (c i && c (i + 2 ^ (k + 1) - 2 ^ j)).toNat) := by
      intro j hj
      rw [hpow j, cycle_power_sum_range_double, mul_sum]
      apply sum_congr rfl
      intro i hi
      have hjk : 2 ^ j ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hp0 := hpow (k + 1)
      have hp1 := hpow j
      have hdiv0 : (2 * i + 2 ^ (k + 1 + 1) - 2 * 2 ^ j) / 2 =
          i + 2 ^ (k + 1) - 2 ^ j := by omega
      have hdiv1 : (2 * i + 1 + 2 ^ (k + 1 + 1) - 2 * 2 ^ j) / 2 =
          i + 2 ^ (k + 1) - 2 ^ j := by omega
      have hd0 : 2 * i / 2 = i := by omega
      have hd1 : (2 * i + 1) / 2 = i := by omega
      rw [hdiv0, hdiv1, hd0, hd1]
      omega
    have ht := sum_congr (s₁ := range (k + 1)) (s₂ := range (k + 1)) rfl (fun j hj => hterm j (mem_range.mp hj))
    have hzero :
        (range (k + 1)).sum (fun j => if j = 0 then 0 else
          (range (2 ^ j)).sum (fun i => (c i && c (i + 2 ^ (k + 1) - 2 ^ j)).toNat)) =
        (range k).sum (fun j =>
          (range (2 ^ (j + 1))).sum (fun i =>
            (c i && c (i + 2 ^ (k + 1) - 2 ^ (j + 1))).toNat)) := by
      rw [show k + 1 = k + 1 by omega, sum_range_succ']
      simp
    have hB :
        (range (k + 1)).sum (fun j =>
          (range (2 ^ j)).sum (fun i => (c i && c (i + 2 ^ (k + 1) - 2 ^ j)).toNat)) =
        (c 0 && c (2 ^ (k + 1) - 1)).toNat +
        (range k).sum (fun j =>
          (range (2 ^ (j + 1))).sum (fun i =>
            (c i && c (i + 2 ^ (k + 1) - 2 ^ (j + 1))).toNat)) := by
      rw [sum_range_succ']
      simp only [pow_zero, sum_range_one, zero_add]
      omega
    rw [ht, ← mul_sum, hB, hzero]
    ring
  unfold cycle_power_dyadic_class_weight
  simp only [Nat.zero_div, hroot]
  rw [hsum]
  omega
