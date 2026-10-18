import AFTD.Prelude
import AFTD.Kb.Tcs.B5QuotientMatrix
import AFTD.Kb.Tcs.G5Adj

/-!
# b5_quotient_trace_sq

Topic: graphs   Node: ca79c09a8d25

Provenance: helper lemma. arXiv:2610.21388 (Stronger spectral bound for clique number), Theorem 2.6 with s = 2 (odd case t = 5); serves b5_clique_bound_iff

tr(M^2) = Σ (n_i - 1)^2 + 2 (n_0 n_1 + n_2 n_3 + n_1 n_3 + n_4 (n_0 + n_1 + n_2 + n_3)) for the quotient matrix of B_5.
-/

theorem b5_quotient_trace_sq (n : Fin 5 → ℕ) :
    (b5_quotient_matrix n ^ 2).trace =
      ∑ i, ((n i : ℝ) - 1) ^ 2 + 2 * ((n 0 : ℝ) * n 1 + n 2 * n 3 + n 1 * n 3 + n 4 * (n 0 + n 1 + n 2 + n 3)) := by
  simp only [Matrix.trace, Matrix.diag_apply, pow_two, Matrix.mul_apply, b5_quotient_matrix, g5_adj]
  simp [Fin.sum_univ_five]
  ring
