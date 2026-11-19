import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SampfordRareGroupRatio

/-!
# sampford_rare_group_ratio_two_two_one

Topic: social_choice   Node: 6a03b0bca610

Provenance: helper lemma. OP-1944

For partition parameters m = 2, r = 2, k = 1, the rare-group coupling deficit ratio is equal to 1/6.
-/

/-- The rare-group coupling deficit ratio for m = 2, r = 2, k = 1 is 1/6. -/
theorem sampford_rare_group_ratio_two_two_one :
    sampfordRareGroupRatio 2 2 1 = 1 / 6 := by
  dsimp [sampfordRareGroupRatio, sampfordRareGroupWeight]
  have h1 : Finset.Ico 2 3 = {2} := by decide
  have h2 : Finset.range 3 = {0, 1, 2} := by decide
  rw [h1, h2]
  norm_num
