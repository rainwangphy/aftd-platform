import AFTD.Prelude
import AFTD.Kb.Tcs.PowerDivergenceExistsBinaryCounterexampleOfLtGoldenRatio
import AFTD.Kb.Tcs.PowerDivergenceGenerator
import AFTD.Kb.Tcs.MutualFInformation

/-!
# mutual_power_divergence_binary_subadditive_imp_golden_ratio_le

Topic: information   Node: 1925b9d9073e

Provenance: original. Related work: arXiv:2610.21231 'On the Subadditivity of Mutual f-Information'

For any positive exponent beta, if the mutual power-divergence information with generator f_beta satisfies subadditivity for all binary Markov chains Y <- X -> Z, then beta >= (Real.sqrt 5 - 1) / 2.
-/

/-- Subadditivity of mutual power-divergence information on binary alphabets implies beta >= (sqrt 5 - 1) / 2. -/
theorem mutual_power_divergence_binary_subadditive_imp_golden_ratio_le (β : ℝ)
    (hβ0 : 0 < β)
    (hsub : ∀ (pX : Fin 2 → ℝ) (PY PZ : Fin 2 → Fin 2 → ℝ),
      (∀ x, 0 ≤ pX x) → (∑ x, pX x = 1) →
      (∀ x y, 0 ≤ PY x y) → (∀ x, ∑ y, PY x y = 1) →
      (∀ x z, 0 ≤ PZ x z) → (∀ x, ∑ z, PZ x z = 1) →
      mutual_f_information (power_divergence_generator β) (fun x (yz : Fin 2 × Fin 2) => pX x * PY x yz.1 * PZ x yz.2) ≤
        mutual_f_information (power_divergence_generator β) (fun x y => pX x * PY x y) +
          mutual_f_information (power_divergence_generator β) (fun x z => pX x * PZ x z)) :
    (Real.sqrt 5 - 1) / 2 ≤ β := by
  by_contra h
  obtain ⟨pX, PY, PZ, hpXpos, hpXsum, hPYpos, hPYsum, hPZpos, hPZsum, hlt⟩ :=
    power_divergence_exists_binary_counterexample_of_lt_golden_ratio β hβ0 (not_le.mp h)
  have hpXnonneg : ∀ x, 0 ≤ pX x := fun x => le_of_lt (hpXpos x)
  have hPYnonneg : ∀ x y, 0 ≤ PY x y := fun x y => le_of_lt (hPYpos x y)
  have hPZnonneg : ∀ x z, 0 ≤ PZ x z := fun x z => le_of_lt (hPZpos x z)
  have hle := hsub pX PY PZ hpXnonneg hpXsum hPYnonneg hPYsum hPZnonneg hPZsum
  linarith
