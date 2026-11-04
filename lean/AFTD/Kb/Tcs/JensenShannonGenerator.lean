import AFTD.Prelude

/-!
# jensen_shannon_generator

Topic: information   Node: 71d96d73164b

Provenance: formalization of a published result. Source: arXiv:2610.21231, Section II, Example 1(3)

The f-divergence generator for Jensen-Shannon divergence is f(x) = (1/2) x log x - ((x + 1)/2) log((x + 1)/2).
-/

/-- The f-divergence generator for Jensen-Shannon divergence with natural logarithms. -/
noncomputable def jensen_shannon_generator (x : ℝ) : ℝ := (1 / 2) * x * Real.log x - ((x + 1) / 2) * Real.log ((x + 1) / 2)
