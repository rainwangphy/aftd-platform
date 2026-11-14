import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicSparseDefectSupport

/-!
# cycle_power_dyadic_sparse_defect_support_card

Topic: combinatorics   Node: 75cdec1821f4

Provenance: helper lemma. RT-1 and OP-205, arXiv:2610.15635. The sparse constant family was identified in experiment 22695; it is a weakened-coverage obstruction, not a full graph-cover model.

For each t≥4, the sparse defect support contains exactly t points.
-/

theorem cycle_power_dyadic_sparse_defect_support_card (t : ℕ) (ht : 4 ≤ t) :
  (cycle_power_dyadic_sparse_defect_support t).card = t := by
  classical
  let q : ℕ := 2^(t-2)
  let T : Finset ℕ := (Finset.range (t-2)).image (fun j => 2^t - 2^j)
  have hq : 4 ≤ q := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ t-2 by omega)
    simpa [q] using h
  have hD : 2^t = 4*q := by
    have ht' : t-2+2 = t := by omega
    calc
      2^t = 2^(t-2+2) := by rw [ht']
      _ = 4*q := by simp [pow_add, q]; ring
  have hbig : ∀ j ∈ Finset.range (t-2), q-1 < 2^t-2^j := by
    intro j hj
    have hj' : j < t-2 := Finset.mem_range.mp hj
    have hp : 2^j < q := by
      dsimp [q]
      exact Nat.pow_lt_pow_right (by decide) hj'
    omega
  have hinj : Set.InjOn (fun j : ℕ => 2^t-2^j) ↑(Finset.range (t-2)) := by
    intro j hj k hk heq
    have hj' : j < t := by have := Finset.mem_range.mp hj; omega
    have hk' : k < t := by have := Finset.mem_range.mp hk; omega
    have hpj : 2^j < 2^t := Nat.pow_lt_pow_right (by decide) hj'
    have hpk : 2^k < 2^t := Nat.pow_lt_pow_right (by decide) hk'
    change 2^t - 2^j = 2^t - 2^k at heq
    have hp : 2^j = 2^k := by omega
    exact (Nat.pow_right_injective (by decide)) hp
  have hcardT : T.card = t-2 := by
    dsimp [T]
    rw [Finset.card_image_iff.mpr hinj, Finset.card_range]
  have hdisj : Disjoint ({0,q-1} : Finset ℕ) T := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (show x ∈ (Finset.range (t-2)).image (fun j => 2^t-2^j) from hy)
    have hb := hbig j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h0 | hq' <;> omega
  have hcardA : ({0,q-1} : Finset ℕ).card = 2 := by
    have hne : (0 : ℕ) ≠ q-1 := by omega
    simp [hne]
  change (({0,q-1} : Finset ℕ) ∪ T).card = t
  rw [Finset.card_union_of_disjoint hdisj, hcardA, hcardT]
  omega
