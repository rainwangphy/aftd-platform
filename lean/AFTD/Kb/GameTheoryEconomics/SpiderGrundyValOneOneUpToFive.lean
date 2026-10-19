import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGrundyVal

/-!
# spider_grundy_val_one_one_up_to_five

Topic: combinatorial_games   Node: f176881b7e7b

Provenance: helper lemma. folklore

For every natural number z with 1 ≤ z and z ≤ 5, the Grundy value spider_grundy_val 1 1 z of the spider tree S(1, 1, z) in the Game of Arrows is equal to z % 2.
-/

/-- The Grundy value of the twin spider S(1, 1, z) in the Game of Arrows equals z % 2 for all 1 ≤ z ≤ 5. -/
theorem spider_grundy_val_one_one_up_to_five (z : ℕ) (h1 : 1 ≤ z) (h5 : z ≤ 5) :
    spider_grundy_val 1 1 z = z % 2 := by
  interval_cases z <;> decide
