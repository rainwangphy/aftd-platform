import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cauchyBinet

Topic: quantum   Node: 4e3746585fe8

Provenance: formalization of a published result. Source: QuantumInfo, `cauchyBinet`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Cauchy–Binet formula** for rectangular matrices: if `A` is `m × n` and `B` is `n × m`, then `det(A * B) = ∑_S det(A[:,S]) * det(B[S,:])` where the sum is over `m`-element subsets `S` of the column/row index.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
set_option maxHeartbeats 400000 in
/-- **Cauchy–Binet formula** for rectangular matrices: if `A` is `m × n` and `B` is `n × m`, then `det(A * B) = ∑_S det(A[:,S]) * det(B[S,:])` where the sum is over `m`-element subsets `S` of the column/row index. -/
lemma cauchyBinet {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    {R : Type*} [CommRing R]
    (A : Matrix (Fin m) n R) (B : Matrix n (Fin m) R) :
    (A * B).det = ∑ S : {S : Finset n // S.card = m},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
      (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  have h_cauchy_binet : ∀ (A : Matrix (Fin m) n R) (B : Matrix n (Fin m) R), Matrix.det (A * B) = ∑ σ : Fin m → n, (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) := by
    simp [Matrix.det_apply']
    simp [Matrix.mul_apply, Finset.mul_sum]
    intro A B; rw [← Finset.sum_comm]; congr; ext x; simp [mul_comm]
    simp only [prod_sum, sum_mul]
    refine' Finset.sum_bij (fun f _ => fun i => f (x.symm i) (Finset.mem_univ _)) _ _ _ _
    · simp
    · simp only [univ_pi_univ, mem_univ, funext_iff, forall_true_left, forall_const]
      exact fun a₁ a₂ h i => by simpa using h (x i)
    · simp only [mem_univ, univ_pi_univ, exists_const, forall_const]
      exact fun b => ⟨fun i _ => b (x i), by ext i; simp⟩
    · simp only [univ_pi_univ, mem_univ, prod_mul_distrib, prod_attach_univ,
      Equiv.symm_apply_apply, forall_const]
      intro a
      rw [← Equiv.prod_comp x.symm]
      ring_nf
      rw [← Equiv.prod_comp x.symm]
      simp only [mul_comm, mul_assoc]
      conv_rhs => rw [← Equiv.prod_comp x]
      simp [Equiv.symm_apply_apply]
  -- Split the sum into injective and non-injective functions.
  have h_split : ∑ σ : Fin m → n, (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) = ∑ σ : Fin m → n, if Function.Injective σ then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0 := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    split_ifs with hσ <;> simp_all [Function.Injective]
    obtain ⟨i, j, hij, hne⟩ := hσ
    exact mul_eq_zero_of_right _ (Matrix.det_zero_of_row_eq hne (by ext1; simp only [of_apply, hij]))
  -- Group the sum by the image of the injective functions.
  have h_group : ∑ σ : Fin m → n, (if Function.Injective σ then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = ∑ S : {S : Finset n // S.card = m}, ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) := by
    rw [← Finset.sum_comm, Finset.sum_congr rfl]
    intro σ _
    by_cases hσ : Function.Injective σ
    · simp [hσ]
      rw [Finset.sum_eq_single ⟨Finset.image σ Finset.univ, by simp [Finset.card_image_of_injective _ hσ]⟩]
      · simp
      · grind
      · simp
    · simp [hσ]
  -- For each subset $S$ of size $m$, the inner sum is equal to the product of the determinants of the submatrices of $A$ and $B$ corresponding to $S$.
  have h_inner : ∀ S : {S : Finset n // S.card = m}, ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = Matrix.det (Matrix.submatrix A id (S.val.orderEmbOfFin S.property)) * Matrix.det (Matrix.submatrix B (S.val.orderEmbOfFin S.property) id) := by
    intro S
    have h_inner_sum : ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = ∑ τ : Equiv.Perm (Fin m), (∏ i, A i (S.val.orderEmbOfFin S.property (τ i))) * Matrix.det (Matrix.of (fun i j ↦ B (S.val.orderEmbOfFin S.property (τ i)) j)) := by
      have h_inner_sum : Finset.filter (fun σ : Fin m → n => Function.Injective σ ∧ Finset.image σ Finset.univ = S.val) Finset.univ = Finset.image (fun τ : Equiv.Perm (Fin m) => fun i => S.val.orderEmbOfFin S.property (τ i)) Finset.univ := by
        ext σ
        simp [Finset.mem_image]
        constructor
        · intro hσ
          obtain ⟨a, ha⟩ : ∃ a : Fin m → Fin m, ∀ i, σ i = S.val.orderEmbOfFin S.property (a i) := by
            have h_exists_a : ∀ i, ∃ a : Fin m, σ i = S.val.orderEmbOfFin S.property a := by
              intro i
              have h_exists_a : σ i ∈ S.val := by
                exact hσ.2 ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
              have h_exists_a : Finset.image (fun a : Fin m => S.val.orderEmbOfFin S.property a) Finset.univ = S.val := by
                refine' Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun a _ => Finset.orderEmbOfFin_mem _ _ _) _
                rw [Finset.card_image_of_injective _ fun a b h => by simpa [Fin.ext_iff] using h]; simp [S.2]
              grind
            exact ⟨fun i => Classical.choose (h_exists_a i), fun i => Classical.choose_spec (h_exists_a i)⟩
          have ha_inj : Function.Injective a := by
            exact fun i j hij => hσ.1 <| by simp [ha, hij]
          exact ⟨Equiv.ofBijective a ⟨ha_inj, Finite.injective_iff_surjective.mp ha_inj⟩, funext fun i => ha i ▸ rfl⟩
        · rintro ⟨a, rfl⟩
          constructor
          · exact fun i j hij => a.injective <| by simpa using hij
          · refine Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun i _ => Finset.orderEmbOfFin_mem _ _ _) ?_
            rw [Finset.card_image_of_injective _ fun i j hij => by simpa [Fin.ext_iff] using hij]; simp [S.2]
      rw [← Finset.sum_filter, h_inner_sum, Finset.sum_image]
      exact fun τ _ τ' _ h => Equiv.Perm.ext fun i => by simpa using congr_fun h i
    rw [h_inner_sum, Matrix.det_apply', Matrix.det_apply']
    simp [Matrix.det_apply', Finset.sum_mul]
    refine' Finset.sum_bij (fun σ _ => σ⁻¹) _ _ _ _ <;> simp [Equiv.Perm.sign_inv]
    · exact fun b => ⟨b⁻¹, inv_inv b⟩
    · intro σ
      rw [← Equiv.prod_comp σ⁻¹]
      simp [mul_assoc, mul_left_comm, Finset.mul_sum]
      refine' Finset.sum_bij (fun τ _ => σ * τ) _ _ _ _ <;> simp [Equiv.Perm.sign_mul]
      · exact fun b => ⟨σ⁻¹ * b, by simp⟩
      · cases' Int.units_eq_one_or (Equiv.Perm.sign σ) with h h <;> simp [h]
  rw [h_cauchy_binet, h_split, h_group, Finset.sum_congr rfl fun S hS => h_inner S]
