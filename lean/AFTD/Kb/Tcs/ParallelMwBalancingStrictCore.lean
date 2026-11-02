import AFTD.Prelude
import AFTD.Kb.Tcs.ParallelMwBalancingTransferBound

/-!
# parallel_mw_balancing_strict_core

Topic: combinatorics   Node: 1d080b48b73b

Provenance: helper lemma. Algebraic reduction for parallel_mw_ratio_decreasing_triple and OP-670.

The stated transfer and numerator bounds imply the strict cross-multiplied balancing inequality when d and N are positive.
-/

theorem parallel_mw_balancing_strict_core (s t A B d N : ℝ)
    (hs : 0 < s) (ht : 2*s ≤ t) (hA : 0 ≤ A) (hB : A ≤ B)
    (hd : 0 < d) (hN : 0 < N)
    (hcases : (d = 1 ∧ B = 2*A) ∨ (d = 2 ∧ B = 4*A) ∨
      (d = 3 ∧ B = 8*A) ∨ 4 ≤ d)
    (hbound : B*(s+t) ≤ 2*N) :
    2*(B-A)*(s*d+t)^2 < N*(2*(s*d+t)*d+d^2) := by
  have htr := parallel_mw_balancing_transfer_bound s t A B d hs.le ht hA hB hcases
  have htpos : 0 < t := by linarith
  have hu : 0 < s*d+t := by positivity
  have h1 := mul_nonneg hu.le (sub_nonneg.mpr htr)
  have h2 := mul_nonneg (mul_nonneg hd.le hu.le) (sub_nonneg.mpr hbound)
  have h3 := mul_pos hN (sq_pos_of_pos hd)
  nlinarith
