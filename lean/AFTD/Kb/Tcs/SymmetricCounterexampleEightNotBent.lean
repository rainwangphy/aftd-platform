import AFTD.Prelude
import AFTD.Kb.Tcs.SymmetricCounterexampleFuncEight
import AFTD.Kb.Tcs.IsBent

/-!
# symmetric_counterexample_eight_not_bent

Topic: combinatorics   Node: 8e3c9c87dac2

Provenance: formalization of a published result. Source: arXiv:2611.06744 Corollary 1

The eight-variable symmetric Boolean function F_8 is not bent.
-/

/-- The eight-variable symmetric Boolean function F_8 is not bent. -/
theorem symmetric_counterexample_eight_not_bent :
    ¬ is_bent symmetric_counterexample_func_eight := by
  intro h
  have h0 := h 0
  revert h0
  decide
