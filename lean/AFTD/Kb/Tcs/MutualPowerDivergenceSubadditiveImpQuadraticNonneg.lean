import AFTD.Prelude
import AFTD.Kb.Tcs.MutualPowerDivergenceSubadditiveImpGoldenRatioLe
import AFTD.Kb.Tcs.GoldenRatioQuadraticNonnegIff
import AFTD.Kb.Tcs.PowerDivergenceGenerator
import AFTD.Kb.Tcs.MutualFInformationSubadditive

/-!
# mutual_power_divergence_subadditive_imp_quadratic_nonneg

Topic: information   Node: e4f1dd489310

Provenance: original. Related work: arXiv:2610.21231 'On the Subadditivity of Mutual f-Information'

For any positive exponent beta, if the mutual power-divergence information with generator f_beta is subadditive under all finite Markov chains Y <- X -> Z, then beta^2 + beta - 1 >= 0.
-/

/-- Subadditivity of mutual power-divergence information implies beta^2 + beta - 1 >= 0. -/
theorem mutual_power_divergence_subadditive_imp_quadratic_nonneg (β : ℝ)
    (hβ0 : 0 < β)
    (hsub : mutual_f_information_subadditive (power_divergence_generator β)) :
    0 ≤ β ^ 2 + β - 1 := by
  rw [golden_ratio_quadratic_nonneg_iff β hβ0]
  exact mutual_power_divergence_subadditive_imp_golden_ratio_le β hβ0 hsub
