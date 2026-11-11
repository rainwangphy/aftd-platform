import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerRootedReflect
import AFTD.Kb.Tcs.CyclePowerRootedReflectExact
import AFTD.Kb.Tcs.CyclePowerRootedReflectCover
import AFTD.Kb.Tcs.CyclePowerReflectShiftedPairDefect
import AFTD.Kb.Tcs.CyclePowerReflectCountDefect
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightReflect

/-!
# cycle_power_dyadic_reflect_defective_half_model

Topic: combinatorics   Node: bd1569ed8854

Provenance: helper lemma. Reflection bridge between the two phase conventions in RT-1.

Reflecting a defective half model reverses its defect function and changes its top-owner phase from shift to half-span minus shift.
-/

theorem cycle_power_dyadic_reflect_defective_half_model (t : ℕ) (ht : 2 ≤ t) (y : ℤ → ℕ → Bool) (e : ℤ → Bool) (shift : ℤ) (hmodel : cycle_power_dyadic_defective_half_model t y e shift) : cycle_power_dyadic_defective_half_model t (cycle_power_rooted_reflect (2^t) y) (fun v => e (-v)) ((2 : ℤ)^(t-1) - shift) := by
  obtain ⟨hweight, hexact, htop, hcover, hcount⟩ := hmodel
  have hp : 0 < (2:ℕ)^t := Nat.two_pow_pos t
  have hhalf : 2^(t-1) + 2^(t-1) = (2:ℕ)^t := by
    have h : t-1+1=t := by omega
    conv_rhs => rw [← h, pow_succ]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p
    change cycle_power_dyadic_class_weight t (fun a => y (-p - ((2^t-1 : ℕ) : ℤ)) (2^t-1-a)) = _
    rw [cycle_power_dyadic_class_weight_reflect, hweight]
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a < 2^t := Finset.mem_range.mp ha
    congr 2
  · intro j hj
    exact cycle_power_rooted_reflect_exact (2^t) (2^j) (Nat.two_pow_pos j)
      (Nat.pow_le_pow_right (by norm_num) (by omega)) y (hexact j hj)
  · intro v
    have h := cycle_power_reflect_shifted_pair_defect (2^t) (2^(t-1))
      (Nat.two_pow_pos _) (by omega) y e shift htop v
    have he : ((2^t - 2^(t-1) : ℕ) : ℤ) = (2 : ℤ)^(t-1) := by
      have hn : 2^t - 2^(t-1) = (2:ℕ)^(t-1) := by omega
      rw [hn]
      norm_cast
    rw [he] at h
    convert h using 1 <;> congr 3 <;> ring
  · intro d hd hdD hne v
    obtain ⟨a,ha,hlo,hhi⟩ := hcover d hd hdD hne (-v-(d : ℤ))
    let b := 2^t-d-1-a
    have hb : b < 2^t-d := by dsimp [b]; omega
    have hi₁ : 2^t-1-b=a+d := by dsimp [b]; omega
    have hi₂ : 2^t-1-(b+d)=a := by dsimp [b]; omega
    have hv : -(v-(b : ℤ))-((2^t-1 : ℕ) : ℤ) = -v-(d : ℤ)-(a : ℤ) := by
      dsimp [b]; omega
    refine ⟨b,hb,?_,?_⟩
    · simpa only [cycle_power_rooted_reflect,hi₁,hv] using hhi
    · simpa only [cycle_power_rooted_reflect,hi₂,hv] using hlo
  · exact cycle_power_reflect_count_defect (2^t) hp y e (t+1) hcount
