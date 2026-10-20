import AFTD.Prelude
import AFTD.Kb.Tcs.Tensor3Pure

/-!
# not_sum_pure_of_linear_flattening_potency_gt

Topic: algebraic_complexity   Node: f77439407116

Provenance: helper lemma. arXiv:2610.08504 Sec. 1

If a linear flattening L on (ℂⁿ)⊗³ and a tensor T satisfy (L T).rank > r * (L(x ⊗ y ⊗ z)).rank for all x, y, z ∈ ℂⁿ, then T cannot be expressed as a sum of r pure tensors.
-/

lemma not_sum_pure_of_linear_flattening_potency_gt_rank_add_le {m n : Type*} [Fintype n]
    (A B : Matrix m n ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank ℂ ↥(A.mulVecLin + B.mulVecLin).range
      ≤ Module.finrank ℂ ↥(A.mulVecLin.range ⊔ B.mulVecLin.range) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ Module.finrank ℂ ↥A.mulVecLin.range + Module.finrank ℂ ↥B.mulVecLin.range :=
        Submodule.finrank_add_le_finrank_add_finrank _ _

lemma not_sum_pure_of_linear_flattening_potency_gt_rank_sum_le {m n : Type*} [Fintype n]
    {ι : Type*} (s : Finset ι) (A : ι → Matrix m n ℂ) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc (A a + ∑ i ∈ s, A i).rank
          ≤ (A a).rank + (∑ i ∈ s, A i).rank :=
            not_sum_pure_of_linear_flattening_potency_gt_rank_add_le _ _
        _ ≤ (A a).rank + ∑ i ∈ s, (A i).rank := by gcongr

/-- A tensor witnessing potency > r for L cannot be expressed as a sum of r pure tensors. -/
theorem not_sum_pure_of_linear_flattening_potency_gt {n u v : ℕ}
    (L : (Fin n → Fin n → Fin n → ℂ) →ₗ[ℂ] Matrix (Fin u) (Fin v) ℂ) (r : ℕ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (hT : ∀ x y z : Fin n → ℂ, r * (L (tensor3_pure x y z)).rank < (L T).rank)
    (x y z : Fin r → Fin n → ℂ) :
    T ≠ ∑ i, tensor3_pure (x i) (y i) (z i) := by
  intro hsum
  classical
  have hL : L T = ∑ i : Fin r, L (tensor3_pure (x i) (y i) (z i)) := by
    rw [hsum, map_sum]
  have hrank : (L T).rank ≤ ∑ i : Fin r, (L (tensor3_pure (x i) (y i) (z i))).rank := by
    rw [hL]
    exact not_sum_pure_of_linear_flattening_potency_gt_rank_sum_le Finset.univ _
  have hlt : ∀ i : Fin r, r * (L (tensor3_pure (x i) (y i) (z i))).rank < (L T).rank :=
    fun i => hT (x i) (y i) (z i)
  by_cases hr : r = 0
  · subst hr
    have hb : (L T).rank ≤ 0 := by simpa using hrank
    have hpos : 0 < (L T).rank := by
      have := hT (fun _ => 0) (fun _ => 0) (fun _ => 0)
      simpa using this
    omega
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hmul :
        r * (∑ i : Fin r, (L (tensor3_pure (x i) (y i) (z i))).rank)
          ≤ r * ((L T).rank - 1) := by
      rw [Finset.mul_sum]
      calc ∑ i : Fin r, r * (L (tensor3_pure (x i) (y i) (z i))).rank
          ≤ ∑ _i : Fin r, ((L T).rank - 1) :=
            Finset.sum_le_sum (fun i _ => Nat.le_sub_one_of_lt (hlt i))
        _ = r * ((L T).rank - 1) := by simp [Finset.sum_const]
    have hle : (∑ i : Fin r, (L (tensor3_pure (x i) (y i) (z i))).rank)
        ≤ (L T).rank - 1 :=
      Nat.le_of_mul_le_mul_left hmul hrpos
    have hbpos : 0 < (L T).rank := by
      have h0 := hlt ⟨0, hrpos⟩
      exact lt_of_le_of_lt (Nat.zero_le _) h0
    omega
