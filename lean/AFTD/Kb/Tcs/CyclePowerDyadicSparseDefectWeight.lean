import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicSparseDefectSupport
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicSparseDefectLowerRank
import AFTD.Kb.Tcs.CyclePowerDyadicSparseDefectPenultimateRank
import AFTD.Kb.Tcs.CyclePowerDyadicSparseDefectTopRank

/-!
# cycle_power_dyadic_sparse_defect_weight

Topic: combinatorics   Node: 49a8e7c788bf

Provenance: helper lemma. RT-1 and OP-205, arXiv:2610.15635. The sparse constant family was identified in experiment 22695; it is a weakened-coverage obstruction, not a full graph-cover model.

The dyadic class weight of the sparse defect support is t for every t≥4.
-/

theorem cycle_power_dyadic_sparse_defect_weight (t : ℕ) (ht : 4 ≤ t) :
  cycle_power_dyadic_class_weight t (fun a => decide (a ∈ cycle_power_dyadic_sparse_defect_support t)) = t := by
  classical
  let S := cycle_power_dyadic_sparse_defect_support t
  let R : ℕ → ℕ := fun j => (Finset.range (2^j)).sum (fun a =>
    (decide (a ∈ S) && decide (a + 2^t - 2^j ∈ S)).toNat)
  have hzero : 0 ∈ S := by simp [S, cycle_power_dyadic_sparse_defect_support]
  have hlast : 2^t-1 ∈ S := by
    change 2^t-1 ∈ ({0,2^(t-2)-1} : Finset ℕ) ∪ (Finset.range (t-2)).image (fun r => 2^t-2^r)
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simp
  have hbase : (∑ j ∈ Finset.range (t-2), if j=0 then 0 else R j) = t-3 := by
    have heq : (∑ j ∈ Finset.range (t-2), if j=0 then 0 else R j) =
        ∑ j ∈ Finset.range (t-2), if j=0 then 0 else 1 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : j=0
      · simp [h]
      · simp only [if_neg h]
        exact cycle_power_dyadic_sparse_defect_lower_rank t j ht (by have := Finset.mem_range.mp hj; omega)
    rw [heq]
    have hn : t-2=(t-3)+1 := by omega
    rw [hn, Finset.sum_range_succ']
    simp
  have hpen : R (t-2) = 1 := cycle_power_dyadic_sparse_defect_penultimate_rank t ht
  have htop : R ((t-2)+1) = 0 := by
    have h : (t-2)+1=t-1 := by omega
    simpa [R,h] using cycle_power_dyadic_sparse_defect_top_rank t ht
  have hne1 : t-2 ≠ 0 := by omega
  have hne2 : (t-2)+1 ≠ 0 := by omega
  have ht' : t=(t-2)+1+1 := by omega
  have htotal : (∑ j ∈ Finset.range t, if j=0 then 0 else R j) = t-2 := by
    conv_lhs => rw [ht', Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [if_neg hne1, if_neg hne2, hbase, hpen, htop]
    omega
  change 2 * (decide (0 ∈ S) && decide (2^t-1 ∈ S)).toNat +
    (∑ j ∈ Finset.range t, if j=0 then 0 else R j) = t
  simp only [hzero, hlast, decide_true, Bool.true_and, Bool.toNat_true, htotal]
  omega
