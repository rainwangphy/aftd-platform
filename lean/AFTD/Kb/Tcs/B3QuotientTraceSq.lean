import AFTD.Prelude
import AFTD.Kb.Tcs.B3QuotientMatrix

/-!
# b3_quotient_trace_sq

Topic: graphs   Node: 8f577cf1b656

Provenance: helper lemma. arXiv:2610.21388 (Stronger spectral bound for clique number), Theorem 2.6 with s = 1; serves b3_sqrt_trace_quotient_sq_le_clique_bound

tr(M^2) = n_0^2 + n_1^2 - n_2^2 + 2 n n_2 + 3 - 2n for the quotient matrix M of B_3(n_0,n_1,n_2), n = n_0 + n_1 + n_2; this is the sum of the squares of the three adjacency eigenvalues of B_3 other than -1.
-/

theorem b3_quotient_trace_sq (n : Fin 3 → ℕ) :
    (b3_quotient_matrix n ^ 2).trace =
      (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 - (n 2 : ℝ) ^ 2 + 2 * (n 0 + n 1 + n 2) * n 2 + 3
        - 2 * (n 0 + n 1 + n 2) := by
  simp [b3_quotient_matrix, Matrix.trace, Fin.sum_univ_three, sq]
  ring
