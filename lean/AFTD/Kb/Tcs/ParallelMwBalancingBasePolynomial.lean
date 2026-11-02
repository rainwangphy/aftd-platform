import AFTD.Prelude

/-!
# parallel_mw_balancing_base_polynomial

Topic: combinatorics   Node: 268d870e8134

Provenance: helper lemma. Algebraic reduction for parallel_mw_ratio_decreasing_triple and OP-670.

A polynomial lower bound under natural-number-style lower bounds on real a and c and exponential proxies A and C.
-/

theorem parallel_mw_balancing_base_polynomial (a c A C : ℝ)
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hA : a + 1 ≤ A) (hC : c + 1 ≤ C)
    (hquad : a^2 + a ≤ 2*A) (hgap : a = 1 ∨ 2 ≤ a)
    (hsmall : a = 1 → A = 2) :
    0 ≤ 4*A^2*C - 10*A - 2*C + 6 - A*(a*(a+2)+2*(a+1)*c) := by
  have hA0 : 0 ≤ A := by linarith
  have hA2 : 2 ≤ A := by linarith
  have hcoef : 0 ≤ 4*A^2 - 2 - 2*A*(a+1) := by
    have hh := mul_nonneg (show 0 ≤ 2*A by positivity) (show 0 ≤ A-(a+1) by linarith)
    nlinarith [sq_nonneg (A-1)]
  have hcoef2 : 0 ≤ 4*A^2 - 2 := by nlinarith [sq_nonneg (A-1)]
  have hm := mul_nonneg (show 0 ≤ c-1 by linarith) hcoef
  have hn := mul_nonneg (show 0 ≤ C-c-1 by linarith) hcoef2
  rcases hgap with h | h
  · have hs := hsmall h
    subst a
    subst A
    nlinarith
  · have hp := mul_nonneg (show 0 ≤ 4*A by positivity) (show 0 ≤ 2*A-(a^2+a) by linarith)
    have hq := mul_nonneg hA0 (show 0 ≤ 3*a^2-12 by nlinarith [sq_nonneg (a-2)])
    nlinarith
