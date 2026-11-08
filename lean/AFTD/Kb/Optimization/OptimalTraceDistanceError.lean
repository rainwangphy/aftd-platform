import AFTD.Prelude
import AFTD.Kb.Optimization.ThermallyReachablePopulations

/-!
# optimal_trace_distance_error

Topic: submodular   Node: 2001a930b5d2

Provenance: formalization of a published result. Source: arXiv:2610.35433, Eq. (36)

The optimal trace-distance approximation error from initial population vector x to target population vector y with respect to Gibbs vector γ, defined as the infimum of (1/2) ‖x' - y‖₁ over all thermally reachable populations x' in thermally_reachable_populations γ x.
-/

/-- The optimal trace-distance approximation error min_{x' ∈ L_γ(x)} (1/2) ‖x' - y‖₁. -/
noncomputable def optimal_trace_distance_error {n : ℕ} (γ x y : Fin n → ℝ) : ℝ := sInf ((fun x' => (1 / 2 : ℝ) * ∑ i : Fin n, |x' i - y i|) '' thermally_reachable_populations γ x)
