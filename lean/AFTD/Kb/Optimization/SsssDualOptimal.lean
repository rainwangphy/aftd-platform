import AFTD.Prelude
import AFTD.Kb.Optimization.SsssDualFeasible
import AFTD.Kb.Optimization.SsssDualObj

/-!
# ssss_dual_optimal

Topic: lp_duality   Node: e433a9958470

Provenance: formalization of a published result. Source: arXiv:2611.26188, Section 3

A dual solution (a, y) is optimal for the LP relaxation (SSSS-D) with k : ℕ paths if it is dual feasible for (E, c, s, t) and for every dual feasible solution (a', y'), the dual objective value ssss_dual_obj s t k a' y' is at most ssss_dual_obj s t k a y.
-/

/-- A dual solution (a, y) is optimal for (SSSS-D) with k paths. -/
def ssss_dual_optimal {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (c : V × V → ℝ) (s t : V) (k : ℕ)
    (a : V → ℝ) (y : Finset V → ℝ) : Prop :=
  ssss_dual_feasible E c s t a y ∧
  ∀ a' y', ssss_dual_feasible E c s t a' y' → ssss_dual_obj s t k a' y' ≤ ssss_dual_obj s t k a y
