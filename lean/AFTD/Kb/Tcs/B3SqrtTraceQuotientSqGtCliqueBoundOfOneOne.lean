import AFTD.Prelude
import AFTD.Kb.Tcs.B3Graph
import AFTD.Kb.Tcs.B3QuotientMatrix
import AFTD.Kb.Tcs.B3QuotientTraceSq
import AFTD.Kb.Tcs.B3CliqueNum

/-!
# b3_sqrt_trace_quotient_sq_gt_clique_bound_of_one_one

Topic: graphs   Node: abbe158c2efa

Provenance: formalization of a published result. Source: arXiv:2610.21388 (Stronger spectral bound for clique number), Theorem 3.1 ("in particular" part: D(1,1,n_3) < 0). Sum of squares of eigenvalues other than -1 stated as tr(M^2) of the quotient matrix

If n_0 = n_1 = 1 and n_2 ≥ 1, then for G = B_3(1, 1, n_2) the bound fails strictly: n(1 - 1/ω(G)) < sqrt(λ_1^2 + λ_2^2 + λ_3^2) (with the sum of squares as tr(M^2)).
-/

theorem b3_sqrt_trace_quotient_sq_gt_clique_bound_of_one_one (n : Fin 3 → ℕ) (h2 : 1 ≤ n 2)
    (h0 : n 0 = 1) (h1 : n 1 = 1) :
    (∑ i, (n i : ℝ)) * (1 - 1 / ((b3_graph n).cliqueNum : ℝ))
      < Real.sqrt ((b3_quotient_matrix n ^ 2).trace) := by
  have hsum : (∑ i, (n i : ℝ)) = (n 2 : ℝ) + 2 := by
    rw [Fin.sum_univ_three, h0, h1]; push_cast; ring
  have hclique : ((b3_graph n).cliqueNum : ℝ) = (n 2 : ℝ) + 1 := by
    rw [b3_cliqueNum, h0, h1]
    have hmax : max (1 + n 2) (1 + n 2) = n 2 + 1 := by omega
    rw [hmax]; push_cast; ring
  have htrace : (b3_quotient_matrix n ^ 2).trace = ((n 2 : ℝ) + 1) ^ 2 := by
    rw [b3_quotient_trace_sq, h0, h1]; push_cast; ring
  rw [hsum, hclique, htrace, Real.sqrt_sq (by positivity)]
  have hfun : ((n 2 : ℝ) + 2) * (1 - 1 / ((n 2 : ℝ) + 1))
      = ((n 2 : ℝ) * ((n 2 : ℝ) + 2)) / ((n 2 : ℝ) + 1) := by
    field_simp; ring
  rw [hfun, div_lt_iff₀ (by positivity)]
  nlinarith
