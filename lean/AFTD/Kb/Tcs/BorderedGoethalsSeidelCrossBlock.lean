import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.CirculantMulBackIdentityMatrixRowSum
import AFTD.Kb.Tcs.SumCompNeg
import AFTD.Kb.Tcs.FinSumSubLeft
import AFTD.Kb.Tcs.GoethalsSeidelArray

/-!
# bordered_goethals_seidel_cross_block

Topic: combinatorics   Node: 039d0fb3c050

Provenance: helper lemma. step of arXiv:2610.27175 Theorem 5 (off-diagonal blocks of H Hᵀ, via row sums 2, 0, 0, 0)

If the first columns a, b, c, d (m > 0) sum to 2, 0, 0, 0, then K Lᵀ + T Mᵀ = 0, where K is the 4 × 4 corner, L the 4m × 4 left border of ±jᵀ, T the top border and M the Goethals-Seidel array of the circulants and the back-identity: the off-diagonal block of H Hᵀ vanishes.
-/

theorem bordered_goethals_seidel_cross_block {m : ℕ} [NeZero m] (a b c d : Fin m → ℤ)
    (hsa : ∑ i, a i = 2) (hsb : ∑ i, b i = 0) (hsc : ∑ i, c i = 0) (hsd : ∑ i, d i = 0) :
    !![(1 : ℤ), -1, -1, -1; -1, 1, -1, -1; -1, -1, 1, -1; -1, -1, -1, 1]
          * (Matrix.of fun (p : Fin 4 × Fin m) (c : Fin 4) =>
              !![(1 : ℤ), 1, 1, 1; -1, 1, 1, -1; -1, -1, 1, 1; -1, 1, -1, 1] p.1 c).transpose
        + (Matrix.of fun (r : Fin 4) (q : Fin 4 × Fin m) =>
              !![(1 : ℤ), 1, 1, 1; 1, -1, 1, -1; 1, -1, -1, 1; 1, 1, -1, -1] r q.1)
          * (goethals_seidel_array (Matrix.circulant a) (Matrix.circulant b) (Matrix.circulant c)
              (Matrix.circulant d) (back_identity_matrix m)).transpose = 0 := by
  ext r ⟨p, i⟩
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    Matrix.of_apply, Matrix.zero_apply]
  simp only [← Finset.mul_sum]
  fin_cases p <;>
    simp [goethals_seidel_array, Fin.sum_univ_four, Matrix.transpose_circulant,
      Finset.sum_neg_distrib, circulant_mul_back_identity_matrix_row_sum,
      sum_comp_neg, fin_sum_sub_left, hsa, hsb, hsc, hsd] <;>
    fin_cases r <;> simp
