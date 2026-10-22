import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.GoethalsSeidelArray
import AFTD.Kb.Tcs.GoethalsSeidelArrayMulTranspose

/-!
# bordered_goethals_seidel_lower_block

Topic: combinatorics   Node: 485c9ec9a1d1

Provenance: helper lemma. step of arXiv:2610.27175 Theorem 5 (bottom-right block of H Hᵀ)

If the circulants A, B, C, D (m > 0) satisfy AAᵀ + BBᵀ + CCᵀ + DDᵀ = (4m+4)I - 4J, then L Lᵀ + M Mᵀ = (4m+4) I for the left border L and the Goethals-Seidel array M of the bordered Goethals-Seidel matrix.
-/

theorem bordered_goethals_seidel_lower_block {m : ℕ} [NeZero m] (a b c d : Fin m → ℤ)
    (hsum : Matrix.circulant a * (Matrix.circulant a).transpose
        + Matrix.circulant b * (Matrix.circulant b).transpose
        + Matrix.circulant c * (Matrix.circulant c).transpose
        + Matrix.circulant d * (Matrix.circulant d).transpose
        = (4 * m + 4 : ℤ) • (1 : Matrix (Fin m) (Fin m) ℤ) - 4 • Matrix.of (fun _ _ => (1 : ℤ))) :
    (Matrix.of fun (p : Fin 4 × Fin m) (c : Fin 4) =>
        !![(1 : ℤ), 1, 1, 1; -1, 1, 1, -1; -1, -1, 1, 1; -1, 1, -1, 1] p.1 c)
      * (Matrix.of fun (p : Fin 4 × Fin m) (c : Fin 4) =>
        !![(1 : ℤ), 1, 1, 1; -1, 1, 1, -1; -1, -1, 1, 1; -1, 1, -1, 1] p.1 c).transpose
      + goethals_seidel_array (Matrix.circulant a) (Matrix.circulant b) (Matrix.circulant c)
          (Matrix.circulant d) (back_identity_matrix m)
        * (goethals_seidel_array (Matrix.circulant a) (Matrix.circulant b) (Matrix.circulant c)
          (Matrix.circulant d) (back_identity_matrix m)).transpose
      = (4 * m + 4 : ℤ) • (1 : Matrix (Fin 4 × Fin m) (Fin 4 × Fin m) ℤ) := by
  rw [goethals_seidel_array_mul_transpose, hsum]
  ext ⟨p, i⟩ ⟨q, j⟩
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply, smul_eq_mul, Prod.mk.injEq, Matrix.transpose_apply]
  fin_cases p <;> fin_cases q <;>
    simp [Fin.sum_univ_four]
