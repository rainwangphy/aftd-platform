import AFTD.Prelude
import AFTD.Kb.Optimization.SsssCuts

/-!
# ssss_dual_obj

Topic: lp_duality   Node: 093d32c261f5

Provenance: formalization of a published result. Source: arXiv:2611.26188, Section 3

The objective value of a dual solution (a, y) for k paths is k * (a(t) - a(s)) plus twice the sum of y_U over all non-empty subsets U of V \ {s, t}.
-/

/-- Objective value of a dual solution (a, y) to (SSSS-D) for k paths. -/
def ssss_dual_obj {V : Type*} [Fintype V] [DecidableEq V]
    (s t : V) (k : ℕ) (a : V → ℝ) (y : Finset V → ℝ) : ℝ := (k : ℝ) * (a t - a s) + ∑ U ∈ ssss_cuts s t, 2 * y U
