import AFTD.Prelude

/-!
# plackett_luce_laplace_profile

Topic: social_choice   Node: 58f68c03b6c3

Provenance: formalization of a published result. Source: OP-1712

For a weight profile w on [0,1], the Laplace profile L(t) is the integral over [0,1] of w(x) * exp(-t * w(x)) dx.
-/

/-- Continuous Laplace profile for a Plackett-Luce weight profile w on [0,1]. -/
noncomputable def plackett_luce_laplace_profile (w : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in Set.Icc (0 : ℝ) 1, w x * Real.exp (-t * w x)
