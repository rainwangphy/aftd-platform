import AFTD.Prelude
import AFTD.Kb.Tcs.PowerDivergenceGenerator
import AFTD.Kb.Tcs.MutualFInformationSubadditive
import AFTD.Kb.Tcs.PowerDivergenceExistsBinaryCounterexampleOfLtGoldenRatio
import AFTD.Kb.Tcs.MutualFInformation

/-!
# mutual_power_divergence_not_subadditive_of_lt_golden_ratio

Topic: information   Node: b5a09f3a1972

Provenance: formalization of a published result. Source: arXiv:2610.21231, On the Subadditivity of Mutual f-Information; Open Problem OP-726

For every exponent beta in (0, (sqrt 5 - 1)/2), the mutual power-divergence information with generator f_beta fails to be subadditive under Markov chains Y <- X -> Z.
-/

/-- Subadditivity fails for mutual power-divergence information for any beta < (sqrt 5 - 1) / 2. -/
theorem mutual_power_divergence_not_subadditive_of_lt_golden_ratio (β : ℝ)
    (hβ0 : 0 < β) (hβ : β < (Real.sqrt 5 - 1) / 2) :
    ¬ mutual_f_information_subadditive (power_divergence_generator β) := by
  intro hsub
  rcases power_divergence_exists_binary_counterexample_of_lt_golden_ratio β hβ0 hβ with
    ⟨pX, PY, PZ, hpX_pos, hpX_sum, hPY_pos, hPY_sum, hPZ_pos, hPZ_sum, hlt⟩
  have hpX_nonneg : ∀ x, 0 ≤ pX x := fun x => (hpX_pos x).le
  have hPY_nonneg : ∀ x y, 0 ≤ PY x y := fun x y => (hPY_pos x y).le
  have hPZ_nonneg : ∀ x z, 0 ≤ PZ x z := fun x z => (hPZ_pos x z).le
  have hle := hsub (Fin 2) (Fin 2) (Fin 2) pX PY PZ hpX_nonneg hpX_sum hPY_nonneg hPY_sum hPZ_nonneg hPZ_sum
  linarith
