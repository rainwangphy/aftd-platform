import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGrundyVal

/-!
# spider_grundy_val_one_one_up_to_seven

Topic: combinatorial_games   Node: b23a89bc9b2c

Provenance: helper lemma. arXiv:2610.15145, Corollary 5.7

For every natural number z with 1 ≤ z and z ≤ 7, the Grundy value spider_grundy_val 1 1 z of the spider tree S(1, 1, z) in the Game of Arrows is equal to z % 2.
-/

/-- The Grundy value of S(1, 1, z) equals z % 2 for all 1 ≤ z ≤ 7. -/
theorem spider_grundy_val_one_one_up_to_seven (z : ℕ) (h1 : 1 ≤ z) (h7 : z ≤ 7) : spider_grundy_val 1 1 z = z % 2 := by
  interval_cases z <;> decide
