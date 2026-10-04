import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxProb
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxValue

/-!
# spi_two_point_max_mid

Topic: mechanism_design   Node: fcfd49d296d8

If E[X] < T <= h, a two-point player's optimal acceptance probability is q(h-l)/(T-l), at posterior mean exactly T.
-/

/-- Between the mean and the high value (`E[X] < T ≤ h`), a two-point player pools: it is accepted with probability `q (h - l) / (T - l)` at posterior mean exactly `T`. -/
lemma spi_two_point_max_mid (h l q T : ℝ) (hT1 : q * h + (1 - q) * l < T) (hT2 : T ≤ h) :
    spi_two_point_max_prob h l q T = q * (h - l) / (T - l) ∧
      spi_two_point_max_value h l q T = T * (q * (h - l) / (T - l)) := by
  unfold spi_two_point_max_prob spi_two_point_max_value
  rw [if_neg (not_le.mpr hT1), if_neg (not_le.mpr hT1), if_pos hT2, if_pos hT2]
  exact ⟨rfl, rfl⟩
