import AFTD.Prelude
import AFTD.Kb.Tcs.ParallelMwBalancingBasePolynomial

/-!
# parallel_mw_balancing_numerator_bound

Topic: combinatorics   Node: 5432d60905fc

Provenance: helper lemma. Algebraic reduction for parallel_mw_ratio_decreasing_triple and OP-670.

Under the displayed size and power inequalities, the triple numerator is at least B times the balanced-endpoint benchmark divided by two.
-/

theorem parallel_mw_balancing_numerator_bound (a c A B C : ℝ)
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hA : a + 1 ≤ A) (hC : c + 1 ≤ C)
    (hquad : a^2 + a ≤ 2*A) (hgap : a = 1 ∨ 2 ≤ a)
    (hsmall : a = 1 → A = 2) (hB : 2*A ≤ B) :
    B*(a*(a+2)+2*(a+1)*c) ≤ 2*(2*A*B*C-2*A-4*B-2*C+6) := by
  have hp := parallel_mw_balancing_base_polynomial a c A C ha hc hA hC hquad hgap hsmall
  have hApos : 0 < A := by linarith
  have hAC : 0 ≤ A+C-3 := by linarith
  have hAk : 0 ≤ A*(4*A*C-8-(a*(a+2)+2*(a+1)*c)) := by nlinarith
  have hk : 0 ≤ 4*A*C-8-(a*(a+2)+2*(a+1)*c) := by
    by_contra hh
    have hn : 4*A*C-8-(a*(a+2)+2*(a+1)*c) < 0 := by linarith
    have hh' := mul_neg_of_pos_of_neg hApos hn
    linarith
  have hm := mul_nonneg (show 0 ≤ B-2*A by linarith) hk
  nlinarith
