import AFTD.Prelude
import AFTD.Kb.Tcs.HnQuotientMatrix
import AFTD.Kb.Tcs.HnPoly
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# hn_quotient_matrix_charpoly

Topic: graphs   Node: 50460a31db3f

Provenance: helper lemma. arXiv:2610.18636:230

For every natural number n, the characteristic polynomial of the quotient matrix hn_quotient_matrix n equals (Polynomial.X + Polynomial.C (n : ℝ)) * hn_poly n.
-/

/-- The characteristic polynomial of the quotient matrix B equals (x + n) q_n(x). -/
theorem hn_quotient_matrix_charpoly (n : ℕ) :
    (hn_quotient_matrix n).charpoly = (Polynomial.X + Polynomial.C (n : ℝ)) * hn_poly n := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three]
  simp [Matrix.charmatrix_apply, Matrix.submatrix, hn_quotient_matrix, hn_poly, Fin.succAbove,
    Matrix.diagonal, Fin.lt_def]
  rw [show (Polynomial.C (2 : ℝ)) = 2 from map_ofNat Polynomial.C 2]
  ring
