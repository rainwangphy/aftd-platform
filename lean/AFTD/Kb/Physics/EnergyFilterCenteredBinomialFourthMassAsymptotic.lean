import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterFloorFourthIntegralLimit
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialFourthStepIntegral
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialFourthRowReindex
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# energy_filter_centered_binomial_fourth_mass_asymptotic

Topic: statistical_mechanics   Node: 6238610ac506

Provenance: helper lemma. OP-892: alternative reduction via centered binomial correlations; experiment 26245.

As k tends to infinity, the fourth power sum of row 2k of Pascal’s triangle, divided by the fourth power of its central coefficient and by √k, tends to √π/2.
-/

theorem energy_filter_centered_binomial_fourth_mass_asymptotic :
    Filter.Tendsto (fun k : ℕ =>
      (∑ j ∈ Finset.range (2 * k + 1), (Nat.choose (2 * k) j : ℝ) ^ 4) /
        ((Nat.choose (2 * k) k : ℝ) ^ 4 * Real.sqrt (k : ℝ)))
      Filter.atTop (nhds (Real.sqrt Real.pi / 2)) := by
  apply energy_filter_floor_fourth_integral_limit.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  rw [energy_filter_centered_binomial_fourth_step_integral k hk,
    energy_filter_centered_binomial_fourth_row_reindex]
  rw [div_div]
