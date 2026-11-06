import AFTD.Prelude
import AFTD.Kb.Tcs.SymmetricCounterexampleFuncEight

/-!
# symmetric_counterexample_eight_ne_zero

Topic: combinatorics   Node: e951a81e3185

Provenance: formalization of a published result. Source: arXiv:2611.06744 Corollary 1

The eight-variable symmetric Boolean function F_8 is not identically zero.
-/

/-- The eight-variable symmetric Boolean function F_8 is not the zero function. -/
theorem symmetric_counterexample_eight_ne_zero :
    symmetric_counterexample_func_eight ≠ 0 := by first | (simp_all; done) | omega | decide | linarith | positivity | (aesop; done)
