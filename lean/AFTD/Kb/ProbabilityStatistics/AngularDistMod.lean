import AFTD.Prelude

/-!
# angular_dist_mod

Topic: minimax   Node: 00a8646ec04a

Provenance: formalization of a published result. Source: arXiv:2611.11852: Section 2

For a natural number q and rotation angles θ₁, θ₂ : ℝ, the angular distance modulo π/q between θ₁ and θ₂ is the infimum over all integers k of |θ₁ - θ₂ - (k : ℝ) * π / (q : ℝ)|.
-/

/-- The angular distance modulo pi/q between two rotation angles theta_1 and theta_2. -/
noncomputable def angular_dist_mod (q : ℕ) (θ₁ θ₂ : ℝ) : ℝ := sInf { |θ₁ - θ₂ - (k : ℝ) * Real.pi / (q : ℝ)| | (k : ℤ) }
