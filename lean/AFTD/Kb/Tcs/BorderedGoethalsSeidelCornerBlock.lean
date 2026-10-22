import AFTD.Prelude

/-!
# bordered_goethals_seidel_corner_block

Topic: combinatorics   Node: f2ac1206e931

Provenance: helper lemma. step of arXiv:2610.27175 Theorem 5 (top-left block of H Hᵀ)

For the bordered Goethals-Seidel matrix: K Kᵀ + T Tᵀ = (4m+4) I₄, where K is the 4 × 4 corner (diagonal 1, off-diagonal -1) and T the 4 × 4m top border of ±j blocks.
-/

theorem bordered_goethals_seidel_corner_block (m : ℕ) :
    !![(1 : ℤ), -1, -1, -1; -1, 1, -1, -1; -1, -1, 1, -1; -1, -1, -1, 1]
        * !![(1 : ℤ), -1, -1, -1; -1, 1, -1, -1; -1, -1, 1, -1; -1, -1, -1, 1].transpose
      + (Matrix.of fun (r : Fin 4) (q : Fin 4 × Fin m) =>
          !![(1 : ℤ), 1, 1, 1; 1, -1, 1, -1; 1, -1, -1, 1; 1, 1, -1, -1] r q.1)
        * (Matrix.of fun (r : Fin 4) (q : Fin 4 × Fin m) =>
          !![(1 : ℤ), 1, 1, 1; 1, -1, 1, -1; 1, -1, -1, 1; 1, 1, -1, -1] r q.1).transpose
      = (4 * m + 4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  ext r r'
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases r <;> fin_cases r' <;>
    simp [Fin.sum_univ_four] <;> ring
