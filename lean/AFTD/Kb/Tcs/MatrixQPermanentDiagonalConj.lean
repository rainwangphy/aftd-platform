import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixQPermanent

/-!
# matrix_q_permanent_diagonal_conj

Topic: combinatorics   Node: adf988ccbe82

Provenance: formalization of a published result. Source: arXiv:2611.14694, Equation (4.2) -- Real positive definite counterexamples to a monotonicity conjecture for the q-permanent

For any natural number n, any n-by-n matrix A over a commutative ring R, any diagonal matrix D = Matrix.diagonal d with d : Fin n → R, and any parameter q in R, the q-permanent of D * A * D equals (Matrix.det D)^2 times the q-permanent of A.
-/

/-- Conjugating a matrix by a diagonal matrix scales its q-permanent by the square of the determinant of the diagonal matrix. -/
theorem matrix_q_permanent_diagonal_conj {n : ℕ} {R : Type*} [CommRing R]
    (q : R) (A : Matrix (Fin n) (Fin n) R) (d : Fin n → R) :
    matrix_q_permanent q (Matrix.diagonal d * A * Matrix.diagonal d) =
      (Matrix.diagonal d).det ^ 2 * matrix_q_permanent q A := by
  have prod_diag_mul_diag : ∀ σ : Equiv.Perm (Fin n),
      ∏ i : Fin n, (Matrix.diagonal d * A * Matrix.diagonal d) i (σ i) =
        (Matrix.diagonal d).det ^ 2 * ∏ i : Fin n, A i (σ i) := by
    intro σ
    have h_entry : ∀ i : Fin n, (Matrix.diagonal d * A * Matrix.diagonal d) i (σ i) = d i * A i (σ i) * d (σ i) := by
      intro i
      rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]
    simp_rw [h_entry]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    rw [Equiv.prod_comp σ d]
    rw [Matrix.det_diagonal]
    ring
  unfold matrix_q_permanent
  simp_rw [prod_diag_mul_diag, mul_left_comm (q ^ _), ← Finset.mul_sum]
