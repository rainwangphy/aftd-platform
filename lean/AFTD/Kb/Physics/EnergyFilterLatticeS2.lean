import AFTD.Prelude

/-!
# energy_filter_lattice_s2

Topic: statistical_mechanics   Node: cde9148562e3

Provenance: original. Related work: arXiv:2405.02158

The discrete lattice sum S_2(tau, h) = sum_{k in Z} exp(-2 tau^2 h^2 k^2) appearing in the rational energy-filter purity limit.
-/

/-- Discrete lattice sum S_2(tau, h) for the rational energy-filter purity limit. -/
noncomputable def energy_filter_lattice_s2 (τ h : ℝ) : ℝ := ∑' (k : ℤ), Real.exp (- 2 * τ^2 * h^2 * (k : ℝ)^2)
