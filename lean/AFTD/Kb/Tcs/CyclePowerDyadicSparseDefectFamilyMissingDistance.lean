import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicSparseDefectSupport
import AFTD.Kb.Tcs.CyclePowerDyadicSparseTwoBandGap

/-!
# cycle_power_dyadic_sparse_defect_family_missing_distance

Topic: combinatorics   Node: 61880a1cb088

Provenance: helper lemma. RT-1 and OP-205, arXiv:2610.15635. The sparse constant family was identified in experiment 22695; it is a weakened-coverage obstruction, not a full graph-cover model.

For every t≥4, no two support points differ by 2^(t−2)−2.
-/

theorem cycle_power_dyadic_sparse_defect_family_missing_distance (t : ℕ) (ht : 4 ≤ t) :
    let q := 2^(t-2)
    let S := cycle_power_dyadic_sparse_defect_support t
    ∀ a ∈ S, ∀ b ∈ S, a < b → b-a ≠ q-2 := by
  let q := 2^(t-2)
  let S := cycle_power_dyadic_sparse_defect_support t
  change ∀ a ∈ S, ∀ b ∈ S, a < b → b-a ≠ q-2
  have hq : 4 ≤ q := by
    dsimp [q]
    calc 4 = 2^2 := by norm_num
      _ ≤ 2^(t-2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2^t = 4*q := by
    dsimp [q]
    have he : t = (t-2)+2 := by omega
    conv_lhs => rw [he, pow_add]
    norm_num
    ring
  have hh : q/2 = 2^(t-3) := by
    dsimp [q]
    have he : t-2 = (t-3)+1 := by omega
    conv_lhs => rw [he, pow_succ]
    omega
  apply cycle_power_dyadic_sparse_two_band_gap q hq S
  intro a ha
  simp only [S, cycle_power_dyadic_sparse_defect_support, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_range] at ha
  rcases ha with (rfl | rfl) | ⟨j, hj, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · right; right
    have hjle : 2^j ≤ 2^(t-3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hh] at hjle
    rw [h4]
    have hp : 0 < 2^j := Nat.two_pow_pos j
    constructor <;> omega
