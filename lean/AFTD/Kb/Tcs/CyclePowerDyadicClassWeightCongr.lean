import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_class_weight_congr

Topic: combinatorics   Node: 9ae8e5799b69

Provenance: helper lemma. Research thread RT-1, OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Helper for cycle_power_dyadic_no_island_of_alternating_paired.

The dyadic class weight cycle_power_dyadic_class_weight m b depends only on the values b i for i < 2^m: if b i = b' i for every i < 2^m, the two weights are equal.
-/

theorem cycle_power_dyadic_class_weight_congr (m : ℕ) (b b' : ℕ → Bool)
    (hb : ∀ i < 2 ^ m, b i = b' i) :
    cycle_power_dyadic_class_weight m b = cycle_power_dyadic_class_weight m b' := open Finset in by
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  unfold cycle_power_dyadic_class_weight
  rw [hb 0 hpos, hb (2 ^ m - 1) (by omega)]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hjm : 2 ^ j ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (le_of_lt (mem_range.mp hj))
  split_ifs
  · rfl
  · apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [hb i (by omega), hb (i + 2 ^ m - 2 ^ j) (by omega)]
