import AFTD.Prelude

/-!
# energy_filter_critical_gaussian_kernel

Topic: statistical_mechanics   Node: a17fe1168c17

Provenance: original. Related work: arXiv:2405.02158, Energy-filtered quantum states and the emergence of non-local correlations

The critical energy filter Gaussian kernel g(x) = 2 * exp(-4 * x^2) / sqrt(pi) on the real line.
-/

/-- The Gaussian kernel g(x) = 2 exp(-4 x^2) / sqrt(pi) appearing in the critical energy-filter crossover law. -/
noncomputable def energy_filter_critical_gaussian_kernel (x : ℝ) : ℝ := 2 * Real.exp (-4 * x^2) / Real.sqrt Real.pi
