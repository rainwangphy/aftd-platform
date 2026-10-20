import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGrundyVal

/-!
# spider_grundy_val_one_three_up_to_three

Topic: combinatorial_games   Node: 4652fa7098d9

Provenance: helper lemma. folklore

For every natural number z with 1 ≤ z and z ≤ 3, the Grundy value spider_grundy_val 1 3 z of the spider tree S(1, 3, z) in the Game of Arrows is equal to z % 2.
-/

/-- The Grundy value of the spider S(1, 3, z) in the Game of Arrows equals z % 2 for all 1 ≤ z ≤ 3. -/
theorem spider_grundy_val_one_three_up_to_three (z : ℕ) (h1 : 1 ≤ z) (h3 : z ≤ 3) :
    spider_grundy_val 1 3 z = z % 2 := by
  interval_cases z <;> decide
