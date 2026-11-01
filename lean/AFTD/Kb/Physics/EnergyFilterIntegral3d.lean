import AFTD.Prelude

/-!
# energy_filter_integral_3d

Topic: statistical_mechanics   Node: e248771ec451

Provenance: helper lemma. step towards energy_filter_two_species_purity_arithmetic_limit

The three-dimensional Gaussian integral I3(k,tau,alpha) = integral over R^3 of exp(-Q(p)/tau^2) times the four factors (4 cos(p_i) cos(alpha p_i))^k and (4 cos(p1+p3-p2) cos(alpha(p1+p3-p2)))^k, where Q(a,b,c) = (3/4)a^2 + b^2 + (3/4)c^2 - ab + (1/2)ac - bc is the minimum of y1^2+y2^2+y3^2+y4^2 subject to y1+y2 = a, y2+y3 = b, y3+y4 = c.
-/

/-- The 3-d Gaussian integral I3 with the quadratic form Q = min of y1^2+y2^2+y3^2+y4^2 over the four-cycle constraints. -/
noncomputable def energy_filter_integral_3d (k : ℕ) (τ α : ℝ) : ℝ := let Q : ℝ × ℝ × ℝ → ℝ := fun p => (3/4) * p.1^2 + p.2.1^2 + (3/4) * p.2.2^2 - p.1 * p.2.1 + (1/2) * p.1 * p.2.2 - p.2.1 * p.2.2
  ∫ p : ℝ × ℝ × ℝ, Real.exp (-(Q p / τ^2)) * (4 * Real.cos p.1 * Real.cos (α * p.1)) ^ k * (4 * Real.cos p.2.1 * Real.cos (α * p.2.1)) ^ k * (4 * Real.cos p.2.2 * Real.cos (α * p.2.2)) ^ k * (4 * Real.cos (p.1 + p.2.2 - p.2.1) * Real.cos (α * (p.1 + p.2.2 - p.2.1))) ^ k
