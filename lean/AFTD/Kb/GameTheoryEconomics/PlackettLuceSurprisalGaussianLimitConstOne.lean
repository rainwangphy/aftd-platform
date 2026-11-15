import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PlackettLuceSurprisalVarianceProfile
import AFTD.Kb.GameTheoryEconomics.PlackettLuceSurprisalVarianceProfileConstOne

/-!
# plackett_luce_surprisal_gaussian_limit_const_one

Topic: social_choice   Node: 52f1ab5dbaba

Provenance: helper lemma. arXiv:2009.09172 (Preference Elicitation as Average-Case Sorting, AAAI 2021)

For the constant weight profile w(x) = 1 on [0,1], the limiting Gaussian distribution gaussianReal with variance Real.toNNReal (plackett_luce_surprisal_variance_profile (fun _ => 1)) degenerates to the Dirac delta measure at 0.
-/

/-- The limiting Gaussian distribution for the constant weight profile w = 1 is Dirac delta at 0. -/
theorem plackett_luce_surprisal_gaussian_limit_const_one :
    ProbabilityTheory.gaussianReal 0 (Real.toNNReal (plackett_luce_surprisal_variance_profile (fun _ => 1))) =
      MeasureTheory.Measure.dirac 0 := by
  rw [plackett_luce_surprisal_variance_profile_const_one, Real.toNNReal_zero]
  exact ProbabilityTheory.gaussianReal_zero_var 0
