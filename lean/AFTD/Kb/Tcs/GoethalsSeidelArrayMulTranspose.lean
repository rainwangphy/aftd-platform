import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.BackIdentityMatrixTranspose
import AFTD.Kb.Tcs.BackIdentityMatrixMulSelf
import AFTD.Kb.Tcs.BackIdentityMatrixMulCirculant
import AFTD.Kb.Tcs.BackIdentityMatrixMulCirculantMul
import AFTD.Kb.Tcs.CirculantMulLeftComm
import AFTD.Kb.Tcs.GoethalsSeidelArray

/-!
# goethals_seidel_array_mul_transpose

Topic: combinatorics   Node: 8f4ef3b78abf

Provenance: helper lemma. arXiv:2610.27175 (Recent progress in the construction of Hadamard matrices), the computation behind Theorem 3; serves Theorem 5

For circulant integer matrices A, B, C, D of order m > 0 and R the back-identity matrix, the Goethals-Seidel array M satisfies M Mᵀ = diag(S, S, S, S) with S = AAᵀ + BBᵀ + CCᵀ + DDᵀ.
-/

theorem goethals_seidel_array_mul_transpose {m : ℕ} [NeZero m] (a b c d : Fin m → ℤ) :
    goethals_seidel_array (Matrix.circulant a) (Matrix.circulant b) (Matrix.circulant c)
        (Matrix.circulant d) (back_identity_matrix m)
      * (goethals_seidel_array (Matrix.circulant a) (Matrix.circulant b) (Matrix.circulant c)
        (Matrix.circulant d) (back_identity_matrix m)).transpose
      = Matrix.of fun p q => if p.1 = q.1 then
          (Matrix.circulant a * (Matrix.circulant a).transpose
            + Matrix.circulant b * (Matrix.circulant b).transpose
            + Matrix.circulant c * (Matrix.circulant c).transpose
            + Matrix.circulant d * (Matrix.circulant d).transpose) p.2 q.2 else 0 := by
  ext ⟨p, i⟩ ⟨q, j⟩
  have key : ∀ (G : Fin 4 → Fin 4 → Matrix (Fin m) (Fin m) ℤ),
      ((Matrix.of fun (p q : Fin 4 × Fin m) => G p.1 q.1 p.2 q.2)
        * (Matrix.of fun (p q : Fin 4 × Fin m) => G p.1 q.1 p.2 q.2).transpose) (p, i) (q, j)
        = (∑ r, G p r * (G q r).transpose) i j := by
    intro G
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.transpose_apply,
      Matrix.of_apply, Matrix.sum_apply]
  rw [goethals_seidel_array, key]
  simp only [Matrix.of_apply]
  fin_cases p <;> fin_cases q <;>
    simp [Fin.sum_univ_four, Matrix.transpose_mul, Matrix.transpose_circulant,
      back_identity_matrix_transpose, Matrix.mul_assoc, back_identity_matrix_mul_circulant_mul,
      back_identity_matrix_mul_circulant, back_identity_matrix_mul_self,
      Matrix.circulant_mul_comm, circulant_mul_left_comm] <;>
    abel_nf
