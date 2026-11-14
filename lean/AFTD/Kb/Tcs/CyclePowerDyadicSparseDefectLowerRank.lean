import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicSparseDefectSupport

/-!
# cycle_power_dyadic_sparse_defect_lower_rank

Topic: combinatorics   Node: e106b541c37c

Provenance: helper lemma. RT-1 and OP-205, arXiv:2610.15635. The sparse constant family was identified in experiment 22695; it is a weakened-coverage obstruction, not a full graph-cover model.

For t≥4 and j<t−2, the unique support pair at dyadic distance 2^t−2^j has first coordinate 0.
-/

theorem cycle_power_dyadic_sparse_defect_lower_rank (t j : ℕ) (ht : 4 ≤ t) (hj : j + 2 < t) :
  (Finset.range (2^j)).sum (fun a =>
    (decide (a ∈ cycle_power_dyadic_sparse_defect_support t) &&
     decide (a + 2^t - 2^j ∈ cycle_power_dyadic_sparse_defect_support t)).toNat) = 1 := by
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
  have h2j : 2 * 2^j ≤ q := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show j+1 ≤ t-2 by omega)
    simpa [q, pow_succ, Nat.mul_comm] using h
  have hlower : ∀ a, a < 2^j → a ∈ cycle_power_dyadic_sparse_defect_support t → a = 0 := by
    intro a ha hmem
    change a ∈ ({0,q-1} : Finset ℕ) ∪ (Finset.range (t-2)).image (fun r => 2^t-2^r) at hmem
    rcases Finset.mem_union.mp hmem with hsmall | hlarge
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hsmall
      rcases hsmall with h0 | hq' <;> omega
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hlarge
      have hr' : r < t-2 := Finset.mem_range.mp hr
      have hp : 2^r < q := by
        dsimp [q]
        exact Nat.pow_lt_pow_right (by decide) hr'
      omega
  have hz : 0 ∈ cycle_power_dyadic_sparse_defect_support t := by
    simp [cycle_power_dyadic_sparse_defect_support]
  have htop : 2^t - 2^j ∈ cycle_power_dyadic_sparse_defect_support t := by
    change 2^t-2^j ∈ ({0,q-1} : Finset ℕ) ∪ (Finset.range (t-2)).image (fun r => 2^t-2^r)
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
  rw [Finset.sum_eq_single 0]
  · simp [hz, htop]
  · intro a ha hne
    have ha' : a < 2^j := Finset.mem_range.mp ha
    have hnot : a ∉ cycle_power_dyadic_sparse_defect_support t := by
      intro hm
      exact hne (hlower a ha' hm)
    simp [hnot]
  · intro hnot
    have hpos : 0 < 2^j := pow_pos (by decide) _
    exact (hnot (Finset.mem_range.mpr hpos)).elim
