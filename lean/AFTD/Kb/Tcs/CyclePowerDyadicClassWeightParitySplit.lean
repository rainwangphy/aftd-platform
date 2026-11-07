import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerSumRangeDouble

/-!
# cycle_power_dyadic_class_weight_parity_split

Topic: combinatorics   Node: 2458defad008

Provenance: helper lemma. Helper for RT-1 (OP-205, arXiv:2610.15635): rungs of cycle_power_dyadic_alternating_half_model (the even and odd halves of the bit-1 classes of an alternating endpoint-only dyadic model form a model one exponent lower)

For any Boolean class b and m >= 1, with D = 2^(m+1): the dyadic class weight of b at exponent m+1, plus [b_0 and b_(D-2)] plus [b_1 and b_(D-1)], equals 2[b_0 and b_(D-1)] plus the weights at exponent m of its even half i -> b_(2i) and of its odd half i -> b_(2i+1). (The even dyadic distances D - 2^j, j >= 1, split by parity into the halves' distances 2^m - 2^(j-1).)
-/

theorem cycle_power_dyadic_class_weight_parity_split (m : ℕ) (hm : 1 ≤ m) (b : ℕ → Bool) :
    cycle_power_dyadic_class_weight (m + 1) b + (b 0 && b (2 ^ (m + 1) - 2)).toNat +
        (b 1 && b (2 ^ (m + 1) - 1)).toNat =
      2 * (b 0 && b (2 ^ (m + 1) - 1)).toNat +
        cycle_power_dyadic_class_weight m (fun i => b (2 * i)) +
        cycle_power_dyadic_class_weight m (fun i => b (2 * i + 1)) := open Finset in by
  have hpow (j : ℕ) : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; omega
  have hD := hpow m
  have hm0 : 0 < 2 ^ m := Nat.two_pow_pos m
  let PE : ℕ → ℕ := fun j => (range (2 ^ j)).sum (fun i => (b (2 * i) && b (2 * (i + 2 ^ m - 2 ^ j))).toNat)
  let PO : ℕ → ℕ := fun j => (range (2 ^ j)).sum (fun i =>
    (b (2 * i + 1) && b (2 * (i + 2 ^ m - 2 ^ j) + 1)).toNat)
  have hL : (range (m + 1)).sum (fun j => if j = 0 then 0 else
        (range (2 ^ j)).sum (fun i => (b i && b (i + 2 ^ (m + 1) - 2 ^ j)).toNat)) =
      (range m).sum (fun j => PE j + PO j) := by
    rw [sum_range_succ']
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_zero]
    apply sum_congr rfl
    intro j hj
    have hjm : 2 ^ j ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (le_of_lt (mem_range.mp hj))
    rw [hpow j, cycle_power_sum_range_double, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    have e0 : 2 * i + 2 ^ (m + 1) - 2 * 2 ^ j = 2 * (i + 2 ^ m - 2 ^ j) := by omega
    have e1 : 2 * i + 1 + 2 ^ (m + 1) - 2 * 2 ^ j = 2 * (i + 2 ^ m - 2 ^ j) + 1 := by omega
    rw [e0, e1]
  have hR : ∀ P : ℕ → ℕ, (range m).sum P = P 0 + (range m).sum (fun j => if j = 0 then 0 else P j) := by
    intro P
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [sum_range_succ', sum_range_succ']
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_zero]
    ring
  have hE : cycle_power_dyadic_class_weight m (fun i => b (2 * i)) =
      2 * (b 0 && b (2 ^ (m + 1) - 2)).toNat + (range m).sum (fun j => if j = 0 then 0 else PE j) := by
    unfold cycle_power_dyadic_class_weight
    have : 2 * (2 ^ m - 1) = 2 ^ (m + 1) - 2 := by omega
    simp only [Nat.mul_zero, this]
    rfl
  have hO : cycle_power_dyadic_class_weight m (fun i => b (2 * i + 1)) =
      2 * (b 1 && b (2 ^ (m + 1) - 1)).toNat + (range m).sum (fun j => if j = 0 then 0 else PO j) := by
    unfold cycle_power_dyadic_class_weight
    have : 2 * (2 ^ m - 1) + 1 = 2 ^ (m + 1) - 1 := by omega
    simp only [Nat.mul_zero, Nat.zero_add, this]
    rfl
  have hE0 : PE 0 = (b 0 && b (2 ^ (m + 1) - 2)).toNat := by
    simp only [PE, pow_zero, sum_range_one, Nat.mul_zero, Nat.zero_add]
    have : 2 * (2 ^ m - 1) = 2 ^ (m + 1) - 2 := by omega
    rw [this]
  have hO0 : PO 0 = (b 1 && b (2 ^ (m + 1) - 1)).toNat := by
    simp only [PO, pow_zero, sum_range_one, Nat.mul_zero, Nat.zero_add]
    have : 2 * (2 ^ m - 1) + 1 = 2 ^ (m + 1) - 1 := by omega
    rw [this]
  have hW : cycle_power_dyadic_class_weight (m + 1) b =
      2 * (b 0 && b (2 ^ (m + 1) - 1)).toNat + (range m).sum (fun j => PE j + PO j) := by
    unfold cycle_power_dyadic_class_weight
    rw [hL]
  rw [hW, hE, hO, sum_add_distrib, hR PE, hR PO, hE0, hO0]
  ring
