import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PlackettLuceLaplaceProfile

/-!
# plackett_luce_limiting_entropy_offset

Topic: social_choice   Node: 9b39bec9b5fd

Provenance: formalization of a published result. Source: OP-1712

The limiting entropy offset mu for a weight profile w is the integral over (0, infinity) of L(t) * log(L(t)) dt minus the integral over [0,1] of log(w(x)) dx, where L is plackett_luce_laplace_profile w.
-/

/-- Limiting entropy offset mu for a smooth weight profile w on [0,1]. -/
noncomputable def plackett_luce_limiting_entropy_offset (w : ℝ → ℝ) : ℝ := (∫ t in Set.Ioi (0 : ℝ), (plackett_luce_laplace_profile w t) * Real.log (plackett_luce_laplace_profile w t)) - (∫ x in Set.Icc (0 : ℝ) 1, Real.log (w x))
