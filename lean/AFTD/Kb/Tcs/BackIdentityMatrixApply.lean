import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix

/-!
# back_identity_matrix_apply

Topic: combinatorics   Node: 4405d917734f

Provenance: helper lemma. sanity lemma for back_identity_matrix; serves bordered_goethals_seidel_is_hadamard

Entry (i, j) of the back-identity matrix is 1 when j is the reversal m - 1 - i of i and 0 otherwise.
-/

theorem back_identity_matrix_apply (m : ℕ) (i j : Fin m) :
    back_identity_matrix m i j = if j = i.rev then 1 else 0 := by
  simp only [back_identity_matrix, Matrix.of_apply, Fin.ext_iff, Fin.val_rev]
  congr 1
  apply propext
  omega
