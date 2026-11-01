import AFTD.Prelude

/-!
# energy_filter_integral_1d

Topic: statistical_mechanics   Node: 9f8957a91146

Provenance: helper lemma. step towards energy_filter_two_species_purity_arithmetic_limit

The one-dimensional Gaussian integral I1(k,tau,alpha) = integral over R of exp(-s^2/(2 tau^2)) * (4 cos s cos(alpha s))^(2k) ds: the integral that carries Tr(M M^T) in the energy-filter purity computation.
-/

/-- The 1-d Gaussian integral I1(k,tau,alpha) = ∫ exp(-s^2/(2τ^2)) (4 cos s cos(αs))^(2k) ds carrying Tr(M M^T). -/
noncomputable def energy_filter_integral_1d (k : ℕ) (τ α : ℝ) : ℝ := ∫ s : ℝ, Real.exp (-(s^2 / (2 * τ^2))) * (4 * Real.cos s * Real.cos (α * s)) ^ (2 * k)
