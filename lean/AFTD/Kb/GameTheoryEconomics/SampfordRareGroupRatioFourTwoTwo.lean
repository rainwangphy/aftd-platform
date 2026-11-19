import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SampfordRareGroupRatio

/-!
# sampford_rare_group_ratio_four_two_two

Topic: social_choice   Node: 34687d49e158

Provenance: helper lemma. OP-1944

For partition parameters m = 4, r = 2, k = 2, the rare-group coupling deficit ratio is equal to 1/5.
-/

/-- The rare-group coupling deficit ratio for m = 4, r = 2, k = 2 is 1/5. -/
theorem sampford_rare_group_ratio_four_two_two :
    sampfordRareGroupRatio 4 2 2 = 1 / 5 := by
  dsimp [sampfordRareGroupRatio, sampfordRareGroupWeight]
  have h1 : Finset.Ico 2 4 = {2, 3} := by decide
  have h2 : Finset.range 4 = {0, 1, 2, 3} := by decide
  rw [h1, h2]
  norm_num [Nat.choose]
