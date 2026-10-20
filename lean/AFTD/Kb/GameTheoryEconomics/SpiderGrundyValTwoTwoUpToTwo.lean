import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGrundyVal

/-!
# spider_grundy_val_two_two_up_to_two

Topic: combinatorial_games   Node: 8e0fab15b727

Provenance: helper lemma. folklore

For every natural number z with 1 ≤ z and z ≤ 2, the Grundy value spider_grundy_val 2 2 z of the spider tree S(2, 2, z) in the Game of Arrows is equal to z % 2.
-/

/-- The Grundy value of the twin spider S(2, 2, z) in the Game of Arrows equals z % 2 for all 1 ≤ z ≤ 2. -/
theorem spider_grundy_val_two_two_up_to_two (z : ℕ) (h1 : 1 ≤ z) (h2 : z ≤ 2) :
    spider_grundy_val 2 2 z = z % 2 := by
  interval_cases z <;> decide
