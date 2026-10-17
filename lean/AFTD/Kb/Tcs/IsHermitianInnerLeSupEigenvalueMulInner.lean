import AFTD.Prelude

/-!
# IsHermitian.inner_le_sup_eigenvalue_mul_inner

Topic: quantum   Node: bdb4d57da9ab

Provenance: formalization of a published result. Source: QuantumInfo, `IsHermitian.inner_le_sup_eigenvalue_mul_inner`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The **Rayleigh quotient bound**: For a Hermitian matrix H with eigenvalues λ, we have `v† H v ≤ (max λ) · v† v` for all v.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- The **Rayleigh quotient bound**: For a Hermitian matrix H with eigenvalues λ, we have `v† H v ≤ (max λ) · v† v` for all v. -/
lemma IsHermitian.inner_le_sup_eigenvalue_mul_inner
    {e : Type*} [Fintype e] [DecidableEq e]
    (H : Matrix e e ℂ) (hH : H.IsHermitian)
    (he : 0 < Fintype.card e)
    (v : e → ℂ) :
    Complex.re (star v ⬝ᵥ H.mulVec v) ≤
    Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp he))
      hH.eigenvalues * Complex.re (star v ⬝ᵥ v) := by
  have := hH.spectral_theorem
  -- Let $w = U^* v$, then $v^* H v = w^* D w$.
  set w : e → ℂ := star (hH.eigenvectorUnitary : Matrix e e ℂ) |> Matrix.mulVec <| v
  have h_eq : (star v ⬝ᵥ H *ᵥ v).re = (star w ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *ᵥ w).re := by
    replace this := congr_arg (fun m => star v ⬝ᵥ m *ᵥ v) this; simp_all [Matrix.mul_assoc]
    simp +zetaDelta at *
    simp [Matrix.dotProduct_mulVec, Matrix.star_mulVec]
    congr! 3
    ext i j; simp [Matrix.mul_apply, Matrix.diagonal]
  -- Since $D$ is diagonal with eigenvalues $\lambda_i$, we have $w^* D w = \sum_{i} \lambda_i |w_i|^2$.
  have h_diag : (star w ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *ᵥ w).re = ∑ i, (hH.eigenvalues i) * ‖w i‖ ^ 2 := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_assoc, mul_comm,]
    simp [Complex.normSq, Complex.sq_norm, diagonal]
    rw [← Finset.sum_sub_distrib]; refine' Finset.sum_congr rfl fun i hi => _; rw [Finset.sum_eq_single i, Finset.sum_eq_single i] <;> simp +contextual; ring_nf
    · exact fun j hj => Or.inl (by rw [if_neg (Ne.symm hj)]; norm_num)
    · exact fun j hj => Or.inl (by rw [if_neg (Ne.symm hj)]; norm_num)
  -- Since $U$ is unitary, we have $\|w\|^2 = \|v\|^2$.
  have h_unitary : ∑ i, ‖w i‖ ^ 2 = (star v ⬝ᵥ v).re := by
    have h_unitary : ∀ (U : Matrix e e ℂ), U.conjTranspose * U = 1 → ∀ (v : e → ℂ), ∑ i, ‖(U.mulVec v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
      intro U hU v
      have h_unitary : (star (U.mulVec v) ⬝ᵥ U.mulVec v) = (star v ⬝ᵥ v) := by
        have h_unitary : (star (U.mulVec v) ⬝ᵥ U.mulVec v) = (star v ⬝ᵥ (Uᴴ * U).mulVec v) := by
          simp [Matrix.mulVec, dotProduct]
          simp [Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul]
          exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm) |> Eq.trans <| Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        rw [h_unitary, hU, Matrix.one_mulVec]
      convert congr_arg Complex.re h_unitary using 1 <;> simp [sq]; ring_nf!
      · simp [dotProduct, sq]; ring_nf!
        simp [Complex.normSq, Complex.sq_norm]; ring_nf!
      · simp [dotProduct]
        simp [← sq, Complex.normSq_apply, Complex.sq_norm]
    convert h_unitary (star (hH.eigenvectorUnitary : Matrix e e ℂ)) _ v using 1 <;> norm_num [Matrix.mulVec, dotProduct]
    · norm_num [Complex.normSq, Complex.sq_norm]
    · simp [Matrix.star_eq_conjTranspose]
      simp [Matrix.IsHermitian.eigenvectorUnitary]
  rw [h_eq, h_diag, ← h_unitary, Finset.mul_sum _ _ _]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (Finset.le_sup' (fun i => hH.eigenvalues i) (Finset.mem_univ i)) (sq_nonneg _)

/- All eigenvalues of `A† A` are bounded by (max singular value)². -/
