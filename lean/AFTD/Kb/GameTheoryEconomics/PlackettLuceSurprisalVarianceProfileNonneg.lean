import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PlackettLuceSurprisalVarianceProfile
import AFTD.Kb.GameTheoryEconomics.PlackettLuceLaplaceProfile

/-!
# plackett_luce_surprisal_variance_profile_nonneg

Topic: social_choice   Node: ae621471703d

Provenance: helper lemma. arXiv:2009.09172 (Preference Elicitation as Average-Case Sorting, AAAI 2021)

For any weight profile w on [0,1], the asymptotic surprisal variance plackett_luce_surprisal_variance_profile w is non-negative.
-/

/-- The asymptotic surprisal variance profile is always non-negative. -/
theorem plackett_luce_surprisal_variance_profile_nonneg (w : ℝ → ℝ) :
    0 ≤ plackett_luce_surprisal_variance_profile w := by
  rw [plackett_luce_surprisal_variance_profile]
  apply MeasureTheory.setIntegral_nonneg measurableSet_Icc
  intro x hx
  exact ProbabilityTheory.variance_nonneg _ (ProbabilityTheory.expMeasure (w x))
