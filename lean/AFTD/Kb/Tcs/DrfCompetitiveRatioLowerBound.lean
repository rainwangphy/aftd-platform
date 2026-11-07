import AFTD.Prelude
import AFTD.Kb.Tcs.DrfProp1RatioTendsto
import AFTD.Kb.Tcs.DrfProp1Alg
import AFTD.Kb.Tcs.DrfProp1OptBound
import AFTD.Kb.Tcs.DrfProp1K
import AFTD.Kb.Tcs.DrfProp1Ratio

/-!
# drf_competitive_ratio_lower_bound

Topic: online_algorithms   Node: 4ed4692cabf0

Provenance: formalization of a published result. Source: arXiv:2611.07905 Proposition 1

For every natural number D with 1 ≤ D and every real number ρ, if for all natural numbers m with 1 ≤ m we have drf_prop1_alg D m ≤ ρ * drf_prop1_opt_bound D m, then 1 + Real.sqrt (D : ℝ) ≤ ρ.
-/

/-- Lower bound of 1 + sqrt(D) on the competitive ratio of Dominant Resource Fairness (Proposition 1, arXiv:2611.07905). -/
theorem drf_competitive_ratio_lower_bound (D : ℕ) (hD : 1 ≤ D) (ρ : ℝ) (hρ : ∀ m : ℕ, 1 ≤ m → drf_prop1_alg D m ≤ ρ * drf_prop1_opt_bound D m) : 1 + Real.sqrt (D : ℝ) ≤ ρ := by
  have htend := drf_prop1_ratio_tendsto D hD
  refine le_of_tendsto htend ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  dsimp [drf_prop1_ratio]
  have hopt : 0 < drf_prop1_opt_bound D m := by
    dsimp [drf_prop1_opt_bound]
    have : (0 : ℝ) < (D : ℝ) := by positivity
    have : (0 : ℝ) < (m : ℝ) := by positivity
    positivity
  exact (div_le_iff₀ hopt).mpr (hρ m hm)
