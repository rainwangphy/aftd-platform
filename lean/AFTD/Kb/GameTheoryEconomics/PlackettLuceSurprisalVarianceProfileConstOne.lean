import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PlackettLuceSurprisalVarianceProfile
import AFTD.Kb.GameTheoryEconomics.PlackettLuceLaplaceProfileConstOne
import AFTD.Kb.GameTheoryEconomics.PlackettLuceLaplaceProfile

/-!
# plackett_luce_surprisal_variance_profile_const_one

Topic: social_choice   Node: eb80e045e113

Provenance: helper lemma. arXiv:2009.09172 (Preference Elicitation as Average-Case Sorting, AAAI 2021)

For the constant weight profile w(x) = 1 on [0,1], the asymptotic surprisal variance plackett_luce_surprisal_variance_profile equals 0.
-/

/-- The asymptotic surprisal variance for the constant weight profile w = 1 is 0. -/
theorem plackett_luce_surprisal_variance_profile_const_one :
    plackett_luce_surprisal_variance_profile (fun _ => 1) = 0 := by
  unfold plackett_luce_surprisal_variance_profile
  simp only [plackett_luce_laplace_profile_const_one, Real.log_exp, one_mul]
  have h : (fun t : ℝ => -t + t) = (fun _ => (0:ℝ)) := by
    funext t; exact neg_add_cancel t
  rw [h]
  change (∫ (x : ℝ) in Set.Icc 0 1,
    ProbabilityTheory.variance (0 : ℝ → ℝ) (ProbabilityTheory.expMeasure (1:ℝ))) = 0
  rw [ProbabilityTheory.variance_zero]
  simp
