import AFTD.Prelude
import AFTD.Kb.Tcs.B4QuotientMatrix

/-!
# b4_quotient_trace_sq

Topic: graphs   Node: 2a4f938f6577

Provenance: formalization of a published result. Source: arXiv:2610.21388, Theorem 2.5

For any n : Fin 4 → ℕ, the trace of the square of b4_quotient_matrix n equals ((n 0 : ℝ) + n 1)^2 + ((n 2 : ℝ) + n 3)^2 + 2 * (n 1 : ℝ) * n 3 - 2 * ((n 0 : ℝ) + n 1 + n 2 + n 3) + 4.
-/

/-- tr(M^2) = (n_0 + n_1)^2 + (n_2 + n_3)^2 + 2 n_1 n_3 - 2(n_0 + n_1 + n_2 + n_3) + 4 for the quotient matrix M of B_4. -/
theorem b4_quotient_trace_sq (n : Fin 4 → ℕ) :
    (b4_quotient_matrix n ^ 2).trace =
      ((n 0 : ℝ) + n 1) ^ 2 + ((n 2 : ℝ) + n 3) ^ 2 + 2 * (n 1 : ℝ) * n 3
        - 2 * ((n 0 : ℝ) + n 1 + n 2 + n 3) + 4 := by
  simp [b4_quotient_matrix, Matrix.trace, Fin.sum_univ_four, pow_two, Matrix.diag_apply]
  ring
