import AFTD.Prelude
import AFTD.Kb.Tcs.B4Graph
import AFTD.Kb.Tcs.B4QuotientMatrix
import AFTD.Kb.Tcs.B4QuotientTraceSq
import AFTD.Kb.Tcs.B4CliqueNum

/-!
# b4_sqrt_trace_quotient_sq_gt_clique_bound_of_one_one

Topic: graphs   Node: 6b718e65b1b2

Provenance: formalization of a published result. Source: arXiv:2610.21388, Section 3, lines 835-851

For n : Fin 4 → ℕ with n 0 = 1, n 1 = 1, n 2 = 1, and n 3 = 1, (∑ i, (n i : ℝ)) * (1 - 1 / ((b4_graph n).cliqueNum : ℝ)) < Real.sqrt ((b4_quotient_matrix n ^ 2).trace).
-/

/-- Failure of the strengthened spectral clique bound for B_4(1, 1, 1, 1) = P_4. -/
theorem b4_sqrt_trace_quotient_sq_gt_clique_bound_of_one_one (n : Fin 4 → ℕ)
    (h0 : n 0 = 1) (h1 : n 1 = 1) (h2 : n 2 = 1) (h3 : n 3 = 1) :
    (∑ i, (n i : ℝ)) * (1 - 1 / ((b4_graph n).cliqueNum : ℝ))
      < Real.sqrt ((b4_quotient_matrix n ^ 2).trace) := by
  have hc : (b4_graph n).cliqueNum = 2 := by
    rw [b4_cliqueNum, h0, h1, h2, h3]
    rfl
  have ht : (b4_quotient_matrix n ^ 2).trace = 6 := by
    rw [b4_quotient_trace_sq, h0, h1, h2, h3]
    norm_num
  have hs : ∑ i : Fin 4, (n i : ℝ) = 4 := by
    rw [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
  rw [hc, ht, hs]
  norm_num
  rw [Real.lt_sqrt (by norm_num)]
  norm_num
