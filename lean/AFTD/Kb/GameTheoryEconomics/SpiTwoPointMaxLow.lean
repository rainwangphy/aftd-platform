import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxProb
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxValue

/-!
# spi_two_point_max_low

Topic: mechanism_design   Node: f5989df0e0ae

If T <= E[X], a two-point player's optimal acceptance probability is 1 and its contribution is E[X].
-/

/-- Below the mean (`T ≤ E[X]`), a two-point player is accepted surely and contributes its mean. -/
lemma spi_two_point_max_low (h l q T : ℝ) (hT : T ≤ q * h + (1 - q) * l) :
    spi_two_point_max_prob h l q T = 1 ∧ spi_two_point_max_value h l q T = q * h + (1 - q) * l := by
  unfold spi_two_point_max_prob spi_two_point_max_value
  rw [if_pos hT, if_pos hT]
  exact ⟨rfl, rfl⟩
