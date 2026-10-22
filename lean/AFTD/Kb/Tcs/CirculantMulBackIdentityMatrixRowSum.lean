import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.MulBackIdentityMatrixApply
import AFTD.Kb.Tcs.CirculantRowSum

/-!
# circulant_mul_back_identity_matrix_row_sum

Topic: combinatorics   Node: ab993b11e41f

Provenance: helper lemma. helper for arXiv:2610.27175 Theorem 5 (row sums of the blocks)

Every row of X R, X the circulant with first column v and R the back-identity, sums to the sum of v.
-/

theorem circulant_mul_back_identity_matrix_row_sum {m : ℕ} [NeZero m] (v : Fin m → ℤ)
    (i : Fin m) :
    ∑ j, (Matrix.circulant v * back_identity_matrix m) i j = ∑ j, v j := by
  simp only [mul_back_identity_matrix_apply]
  rw [← circulant_row_sum v i]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)
