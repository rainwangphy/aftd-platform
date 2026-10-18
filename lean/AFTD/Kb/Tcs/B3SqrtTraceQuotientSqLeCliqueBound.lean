import AFTD.Prelude
import AFTD.Kb.Tcs.B3Graph
import AFTD.Kb.Tcs.B3QuotientMatrix
import AFTD.Kb.Tcs.B3QuotientTraceSq
import AFTD.Kb.Tcs.B3CliqueNum
import AFTD.Kb.Tcs.B3SqLe

/-!
# b3_sqrt_trace_quotient_sq_le_clique_bound

Topic: graphs   Node: cc301ad656bd

Provenance: formalization of a published result. Source: arXiv:2610.21388 (Stronger spectral bound for clique number), Theorem 3.1 (first part). The Lean states the sum of squares of the three eigenvalues other than -1 as tr(M^2) for the quotient matrix M (Theorems 2.3 and 2.6); ω is Mathlib's cliqueNum of the graph; proof differs from the paper's (nlinarith instead of derivative analysis)

Let n_0, n_1, n_2 be positive integers with (n_0, n_1) ≠ (1, 1), G = B_3(n_0, n_1, n_2) of order n = n_0 + n_1 + n_2, and λ_1, λ_2, λ_3 the adjacency eigenvalues of G other than -1 (the eigenvalues of the quotient matrix M). Then sqrt(λ_1^2 + λ_2^2 + λ_3^2) ≤ n(1 - 1/ω(G)). In Lean λ_1^2 + λ_2^2 + λ_3^2 is tr(M^2) and ω(G) is the clique number of the graph.
-/

theorem b3_sqrt_trace_quotient_sq_le_clique_bound (n : Fin 3 → ℕ) (hpos : ∀ i, 1 ≤ n i)
    (h11 : ¬ (n 0 = 1 ∧ n 1 = 1)) :
    Real.sqrt ((b3_quotient_matrix n ^ 2).trace)
      ≤ (∑ i, (n i : ℝ)) * (1 - 1 / ((b3_graph n).cliqueNum : ℝ)) := by
  rw [b3_quotient_trace_sq, b3_cliqueNum, Fin.sum_univ_three]
  exact b3_sq_le (n 0) (n 1) (n 2) (hpos 0) (hpos 1) (hpos 2) h11
