import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixPermanentSuccRowZero

/-!
# matrix_permanent_succ_row

Topic: algebraic_complexity   Node: f98145cc70cc

Provenance: original. Related work: Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:771

For any commutative semiring R, any natural number n, any square matrix A of size (n+1) x (n+1) over R, and any row index i : Fin (n+1), the permanent of A equals the sum over all columns j : Fin (n+1) of A i j times the permanent of the submatrix obtained by deleting row i and column j: permanent A = ∑ j : Fin (n+1), A i j * permanent (A.submatrix i.succAbove j.succAbove).
-/

/-- Laplacian expansion of the permanent of an (n+1) x (n+1) matrix along row i. -/
theorem matrix_permanent_succ_row {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n.succ) (Fin n.succ) R) (i : Fin n.succ) :
    A.permanent = ∑ j : Fin n.succ, A i j * (A.submatrix i.succAbove j.succAbove).permanent := by
  rw [← Matrix.permanent_permute_cols i.cycleRange⁻¹, matrix_permanent_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.submatrix_apply, Matrix.submatrix_submatrix, Equiv.Perm.inv_def]
  have h1 : i.cycleRange.symm 0 = i := Fin.cycleRange_symm_zero i
  have h2 : (⇑i.cycleRange.symm ∘ Fin.succ) = i.succAbove := funext (Fin.cycleRange_symm_succ i)
  have h3 : (id ∘ j.succAbove) = j.succAbove := rfl
  rw [h1, h2, h3]
  rfl
