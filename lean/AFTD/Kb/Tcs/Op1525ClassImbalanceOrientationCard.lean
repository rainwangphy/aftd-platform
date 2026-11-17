import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op1525_class_imbalance_orientation_card

Topic: combinatorics   Node: 7a6e7d31177a

Provenance: helper lemma. A component of the complete-multipartite reconstruction route for OP-1525 and arXiv:2611.13901.

For more than two signed vertices partitioned into classes, if some class has nonzero signed sum, there is a vertex whose switched class-sum vector cannot be obtained by changing one coordinate of the negated original class-sum vector by either two or minus two.
-/

theorem op1525_class_imbalance_orientation_card
    {V J : Type*} [DecidableEq J] [Fintype V] [Fintype J]
    (cl : V → J) (f : V → ℤ)
    (hsgn : ∀ v, f v = 1 ∨ f v = -1)
    (hsize : 2 < Fintype.card V)
    (hnonzero : ∃ j : J, (∑ v : V, if cl v = j then f v else 0) ≠ 0) :
    ∃ v : V, ∀ (j : J) (s : ℤ), (s = 1 ∨ s = -1) → ∃ k : J,
      (∑ u : V, if cl u = k then f u else 0) -
          2 * (if cl v = k then f v else 0) ≠
        -(∑ u : V, if cl u = k then f u else 0) +
          2 * (if j = k then s else 0) := by
  classical
  let D : J → ℤ := fun j => ∑ v : V, if cl v = j then f v else 0
  let S : ℤ := ∑ v : V, f v
  change (∃ j, D j ≠ 0) at hnonzero
  change ∃ v, ∀ j s, (s = 1 ∨ s = -1) → ∃ k,
    D k - 2 * (if cl v = k then f v else 0) ≠
      -D k + 2 * (if j = k then s else 0)
  by_contra H
  push_neg at H
  have hDsum : (∑ j : J, D j) = S := by
    dsimp [D, S]
    rw [Finset.sum_comm]
    simp
  have hu (v : V) : ∃ j : J, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ k : J, D k = (if cl v = k then f v else 0) + (if j = k then s else 0) := by
    obtain ⟨j,s,hs,hall⟩ := H v
    refine ⟨j,s,hs,?_⟩
    intro k
    have hk := hall k
    omega
  have hsum (v : V) : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ S = f v + s := by
    obtain ⟨j,s,hs,hall⟩ := hu v
    refine ⟨s,hs,?_⟩
    calc
      S = ∑ k : J, D k := hDsum.symm
      _ = ∑ k : J, ((if cl v = k then f v else 0) + (if j = k then s else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        exact hall k
      _ = f v + s := by
        simp [Finset.sum_add_distrib, eq_comm]
  have hnonempty : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v0 : V := Classical.choice hnonempty
  have hcases : S = 0 ∨ S = 2 ∨ S = -2 := by
    obtain ⟨s, hs, heq⟩ := hsum v0
    rcases hsgn v0 with h | h <;> rcases hs with hs | hs <;> omega
  have hS : S = 0 := by
    rcases hcases with hz | hp | hn
    · exact hz
    · have hall : ∀ v, f v = 1 := by
        intro v
        obtain ⟨s,hs,heq⟩ := hsum v
        rcases hsgn v with h | h <;> rcases hs with hs | hs <;> omega
      have hcard : S = (Fintype.card V : ℤ) := by simp [S, hall]
      omega
    · have hall : ∀ v, f v = -1 := by
        intro v
        obtain ⟨s,hs,heq⟩ := hsum v
        rcases hsgn v with h | h <;> rcases hs with hs | hs <;> omega
      have hcard : S = -(Fintype.card V : ℤ) := by simp [S, hall]
      omega
  have hdiff (v : V) : ∃ j : J, j ≠ cl v ∧ ∀ k : J,
      D k = (if cl v = k then f v else 0) - (if j = k then f v else 0) := by
    obtain ⟨j,s,hs,hall⟩ := hu v
    have hSv : S = f v + s := by
      calc
        S = ∑ k : J, D k := hDsum.symm
        _ = ∑ k : J, ((if cl v = k then f v else 0) + (if j = k then s else 0)) := by
          apply Finset.sum_congr rfl
          intro k _
          exact hall k
        _ = f v + s := by
          simp [Finset.sum_add_distrib, eq_comm]
    have hsneg : s = -f v := by omega
    have hd (k : J) : D k = (if cl v = k then f v else 0) - (if j = k then f v else 0) := by
      rw [hall k, hsneg]
      split_ifs <;> ring
    have hj : j ≠ cl v := by
      intro hj
      obtain ⟨k,hk⟩ := hnonzero
      have hz := hd k
      simp [hj] at hz
      exact hk hz
    exact ⟨j,hj,hd⟩
  have hdiag (v : V) : D (cl v) = f v := by
    obtain ⟨j,hj,hd⟩ := hdiff v
    simpa [hj] using hd (cl v)
  have hsq (v : V) : f v * f v = 1 := by
    rcases hsgn v with h | h <;> rw [h] <;> norm_num
  have hsum1 : (∑ v : V, f v * D (cl v)) = (Fintype.card V : ℤ) := by
    simp only [hdiag, hsq, Finset.sum_const_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  obtain ⟨j0,hj0,hd0⟩ := hdiff v0
  have hsum2 : (∑ v : V, f v * D (cl v)) = f v0 * (D (cl v0) - D j0) := by
    change (∑ v : V, f v * D (cl v)) =
      f v0 * ((∑ v : V, if cl v = cl v0 then f v else 0) -
        (∑ v : V, if cl v = j0 then f v else 0))
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [hd0 (cl v)]
    simp only [mul_sub, mul_ite, mul_zero]
    simp [eq_comm, mul_comm]
  have hjval : D j0 = -f v0 := by
    have h := hd0 j0
    simpa [hj0, Ne.symm hj0] using h
  have hsquare := hsq v0
  rw [hdiag v0, hjval] at hsum2
  have hc : (Fintype.card V : ℤ) = 2 := by nlinarith [hsum1, hsum2, hsquare]
  omega
