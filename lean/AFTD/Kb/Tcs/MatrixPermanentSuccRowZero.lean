import AFTD.Prelude

/-!
# matrix_permanent_succ_row_zero

Topic: algebraic_complexity   Node: 1f075b21e85d

Provenance: helper lemma. Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:763

For any commutative semiring R, any natural number n, and any square matrix A of size (n+1) x (n+1) over R, the permanent of A equals the sum over all columns j : Fin (n+1) of A 0 j times the permanent of the submatrix obtained by deleting row 0 and column j: permanent A = ∑ j : Fin (n+1), A 0 j * permanent (A.submatrix Fin.succ j.succAbove).
-/

theorem matrix_permanent_succ_row_zero_column_zero {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    A.permanent = ∑ i : Fin n.succ, A i 0 * (A.submatrix i.succAbove Fin.succ).permanent := by
  rw [Matrix.permanent, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.prod_univ_succ, Matrix.permanent, Finset.mul_sum,
      Equiv.Perm.decomposeFin_symm_apply_zero,
      Equiv.swap_self, id,
      Equiv.Perm.decomposeFin_symm_apply_succ, Fin.succAbove_zero, Equiv.coe_refl,
      Matrix.of_apply]
  · rw [← Matrix.permanent_permute_cols (Fin.cycleRange i), Matrix.permanent, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Fin.prod_univ_succ, Fin.succAbove_cycleRange,
      Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
      Matrix.submatrix_apply, Matrix.of_apply, id]

/-- Laplacian expansion of the permanent of an (n+1) x (n+1) matrix along row 0. -/
theorem matrix_permanent_succ_row_zero {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    A.permanent = ∑ j : Fin n.succ, A 0 j * (A.submatrix Fin.succ j.succAbove).permanent := by
  rw [← Matrix.permanent_transpose A, matrix_permanent_succ_row_zero_column_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.permanent_transpose]
  simp only [Matrix.transpose_apply, Matrix.transpose_submatrix, Matrix.transpose_transpose]
