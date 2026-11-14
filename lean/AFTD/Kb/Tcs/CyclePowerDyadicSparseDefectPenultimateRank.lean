import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicSparseDefectSupport

/-!
# cycle_power_dyadic_sparse_defect_penultimate_rank

Topic: combinatorics   Node: d8f23e333857

Provenance: helper lemma. RT-1 and OP-205, arXiv:2610.15635. The sparse constant family was identified in experiment 22695; it is a weakened-coverage obstruction, not a full graph-cover model.

At t≥4, there is exactly one support pair at distance 2^t−2^(t−2).
-/

private theorem rt1_sparse_bounds865 (t : ℕ) (ht : 4 ≤ t) :
    let q := 2^(t-2)
    4 ≤ q ∧ 2^t = 4*q ∧
      ∀ a, a ≤ 3*q → a ∈ cycle_power_dyadic_sparse_defect_support t → a = 0 ∨ a = q-1 := by
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
  refine ⟨hq,hD,?_⟩
  intro a ha hmem
  change a ∈ ({0,q-1} : Finset ℕ) ∪ (Finset.range (t-2)).image (fun r => 2^t-2^r) at hmem
  rcases Finset.mem_union.mp hmem with hsmall | hlarge
  · simpa only [Finset.mem_insert, Finset.mem_singleton] using hsmall
  · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hlarge
    have hr' : r < t-2 := Finset.mem_range.mp hr
    have hp : 2^r < q := by
      dsimp [q]
      exact Nat.pow_lt_pow_right (by decide) hr'
    omega

theorem cycle_power_dyadic_sparse_defect_penultimate_rank (t : ℕ) (ht : 4 ≤ t) :
  (Finset.range (2^(t-2))).sum (fun a =>
    (decide (a ∈ cycle_power_dyadic_sparse_defect_support t) &&
     decide (a + 2^t - 2^(t-2) ∈ cycle_power_dyadic_sparse_defect_support t)).toNat) = 1 := by
  classical
  let q : ℕ := 2^(t-2)
  obtain ⟨hq,hD,hsmall⟩ := rt1_sparse_bounds865 t ht
  change (Finset.range q).sum (fun a =>
    (decide (a ∈ cycle_power_dyadic_sparse_defect_support t) &&
     decide (a + 2^t - q ∈ cycle_power_dyadic_sparse_defect_support t)).toNat) = 1
  have hsmallmem : q-1 ∈ cycle_power_dyadic_sparse_defect_support t := by
    change q-1 ∈ ({0,q-1} : Finset ℕ) ∪ (Finset.range (t-2)).image (fun r => 2^t-2^r)
    simp
  have htopmem : 2^t-1 ∈ cycle_power_dyadic_sparse_defect_support t := by
    change 2^t-1 ∈ ({0,q-1} : Finset ℕ) ∪ (Finset.range (t-2)).image (fun r => 2^t-2^r)
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simp
  have hnot3q : 3*q ∉ cycle_power_dyadic_sparse_defect_support t := by
    intro hm
    have h := hsmall (3*q) (by omega) hm
    omega
  rw [Finset.sum_eq_single (q-1)]
  · have heq : (q-1)+2^t-q = 2^t-1 := by omega
    simp [hsmallmem, heq, htopmem]
  · intro a ha hne
    have ha' : a < q := Finset.mem_range.mp ha
    by_cases hm : a ∈ cycle_power_dyadic_sparse_defect_support t
    · have hs := hsmall a (by omega) hm
      have ha0 : a=0 := by omega
      have heq : a+2^t-q = 3*q := by omega
      simp [heq,hnot3q]
    · simp [hm]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim
