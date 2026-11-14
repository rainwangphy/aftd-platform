import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PlackettLuceLaplaceProfile

/-!
# plackett_luce_surprisal_variance_profile

Topic: social_choice   Node: 63bf97478416

Provenance: formalization of a published result. Source: OP-1712

The asymptotic surprisal variance V for a weight profile w is the integral over x in [0,1] of the variance of log(L(X_x)) + w(x) * X_x, where L is plackett_luce_laplace_profile w and X_x has the exponential distribution of rate w(x).
-/

/-- Asymptotic surprisal variance V for a smooth weight profile w on [0,1]. -/
noncomputable def plackett_luce_surprisal_variance_profile (w : ℝ → ℝ) : ℝ := ∫ x in Set.Icc (0 : ℝ) 1, ProbabilityTheory.variance (fun t => Real.log (plackett_luce_laplace_profile w t) + w x * t) (ProbabilityTheory.expMeasure (w x))
