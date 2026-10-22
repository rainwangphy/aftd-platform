import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.BackIdentityMatrixApply

/-!
# mul_back_identity_matrix_apply

Topic: combinatorics   Node: 4124301a4fd2

Provenance: helper lemma. helper for bordered_goethals_seidel_is_hadamard (arXiv:2610.27175 Theorem 5)

Right multiplication by the back-identity matrix reverses the columns: (X R) i j = X i (m - 1 - j).
-/

theorem mul_back_identity_matrix_apply {m : ℕ} (X : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) :
    (X * back_identity_matrix m) i j = X i j.rev := by
  simp only [Matrix.mul_apply, back_identity_matrix_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro k _ hk
    rw [if_neg]
    intro h
    exact hk (by rw [h, Fin.rev_rev])
  · simp
