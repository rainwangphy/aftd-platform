import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicSparseDefectSupport

/-!
# cycle_power_dyadic_sparse_defect_two_covered_distances

Topic: combinatorics   Node: 3bc4897cd48a

Provenance: helper lemma. RT-1 and OP-205, arXiv:2610.15635. The sparse constant family was identified in experiment 22695; it is a weakened-coverage obstruction, not a full graph-cover model.

For each t≥4, the support covers distances 1 and 3·2^(t−2)−1.
-/

theorem cycle_power_dyadic_sparse_defect_two_covered_distances (t : ℕ) (ht : 4 ≤ t) :
  (∃ a ∈ cycle_power_dyadic_sparse_defect_support t, ∃ b ∈ cycle_power_dyadic_sparse_defect_support t, a < b ∧ b-a = 1) ∧
  (∃ a ∈ cycle_power_dyadic_sparse_defect_support t, ∃ b ∈ cycle_power_dyadic_sparse_defect_support t, a < b ∧ b-a = 3 * 2^(t-2)-1) := by
  classical
  let q : ℕ := 2^(t-2)
  have hq : 4 ≤ q := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ t-2 by omega)
    simpa [q] using h
  have hD : 2^t = 4*q := by
    have ht' : t-2+2 = t := by omega
    calc
      2^t = 2^(t-2+2) := by rw [ht']
      _ = 4*q := by simp [pow_add, q]; ring
  have hsmall : q-1 ∈ cycle_power_dyadic_sparse_defect_support t := by
    change q-1 ∈ ({0,q-1} : Finset ℕ) ∪ (Finset.range (t-2)).image (fun r => 2^t-2^r)
    simp
  have hD1 : 2^t-1 ∈ cycle_power_dyadic_sparse_defect_support t := by
    change 2^t-1 ∈ ({0,q-1} : Finset ℕ) ∪ (Finset.range (t-2)).image (fun r => 2^t-2^r)
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simp
  have hD2 : 2^t-2 ∈ cycle_power_dyadic_sparse_defect_support t := by
    change 2^t-2 ∈ ({0,q-1} : Finset ℕ) ∪ (Finset.range (t-2)).image (fun r => 2^t-2^r)
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
    norm_num
  constructor
  · exact ⟨2^t-2, hD2, 2^t-1, hD1, by omega, by omega⟩
  · change ∃ a ∈ cycle_power_dyadic_sparse_defect_support t, ∃ b ∈ cycle_power_dyadic_sparse_defect_support t, a < b ∧ b-a = 3*q-1
    exact ⟨q-1, hsmall, 2^t-2, hD2, by omega, by omega⟩
