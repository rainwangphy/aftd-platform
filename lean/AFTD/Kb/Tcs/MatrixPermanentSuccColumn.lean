import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixPermanentSuccRow

/-!
# matrix_permanent_succ_column

Topic: algebraic_complexity   Node: 4d4c8ca345bd

Provenance: formalization of a published result. Source: Minc, Permanents, Encyclopedia of Mathematics and its Applications, Addison-Wesley, 1978, Section 1.2

For any commutative semiring R, any natural number n, any square matrix A of size (n+1) x (n+1) over R, and any column index j : Fin (n+1), the permanent of A equals the sum over all row indices i : Fin (n+1) of A i j times the permanent of the submatrix obtained by deleting row i and column j: A.permanent = ∑ i : Fin n.succ, A i j * (A.submatrix i.succAbove j.succAbove).permanent.
-/

/-- Laplace column expansion for the permanent over a commutative semiring. -/
theorem matrix_permanent_succ_column {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n.succ) (Fin n.succ) R) (j : Fin n.succ) :
    A.permanent = ∑ i : Fin n.succ, A i j * (A.submatrix i.succAbove j.succAbove).permanent := by
  rw [← Matrix.permanent_transpose A]
  rw [matrix_permanent_succ_row A.transpose j]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.transpose_apply]
  congr 1
  rw [← Matrix.permanent_transpose (A.submatrix i.succAbove j.succAbove)]
  rw [Matrix.transpose_submatrix]
