import AFTD.Prelude
import AFTD.Kb.Tcs.MutualPowerDivergenceBinarySubadditiveImpGoldenRatioLe
import AFTD.Kb.Tcs.MutualFInformationSubadditive
import AFTD.Kb.Tcs.PowerDivergenceGenerator

/-!
# mutual_power_divergence_subadditive_imp_golden_ratio_le

Topic: information   Node: 264a47a78c83

Provenance: original. Related work: arXiv:2610.21231 'On the Subadditivity of Mutual f-Information'

For any positive exponent beta, if the mutual power-divergence information with generator f_beta is subadditive under all finite Markov chains Y <- X -> Z, then beta >= (Real.sqrt 5 - 1) / 2.
-/

/-- Subadditivity of mutual power-divergence information across all finite alphabets implies beta >= (sqrt 5 - 1) / 2. -/
theorem mutual_power_divergence_subadditive_imp_golden_ratio_le (β : ℝ)
    (hβ0 : 0 < β)
    (hsub : mutual_f_information_subadditive (power_divergence_generator β)) :
    (Real.sqrt 5 - 1) / 2 ≤ β := mutual_power_divergence_binary_subadditive_imp_golden_ratio_le β hβ0 (hsub (Fin 2) (Fin 2) (Fin 2))
