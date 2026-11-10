import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_class_weight_reflect

Topic: combinatorics   Node: b336b7b87c27

Provenance: helper lemma. Defective half-model reduction for research thread RT-1.

The dyadic class weight is invariant under reversing the offset interval.
-/

open Finset

theorem cycle_power_dyadic_class_weight_reflect (t : ℕ) (b : ℕ → Bool) :
    cycle_power_dyadic_class_weight t (fun a => b (2^t-1-a)) =
      cycle_power_dyadic_class_weight t b := by
  have hpos : 0 < (2:ℕ)^t := Nat.two_pow_pos t
  unfold cycle_power_dyadic_class_weight
  simp only [Nat.sub_zero]
  have he : 2^t-1-(2^t-1)=0 := by omega
  rw [he, Bool.and_comm (b (2^t-1)) (b 0)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with hj0
  · rfl
  · have hjt : j < t := Finset.mem_range.mp hj
    have hjpow : (2:ℕ)^j ≤ 2^t := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hL : 0 < (2:ℕ)^j := Nat.two_pow_pos j
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro a ha
    have haL : a < 2^j := Finset.mem_range.mp ha
    have hidx₁ : 2^t-1-(2^j-1-a)=a+2^t-2^j := by omega
    have hidx₂ : 2^t-1-((2^j-1-a)+2^t-2^j)=a := by omega
    rw [hidx₁,hidx₂,Bool.and_comm]
