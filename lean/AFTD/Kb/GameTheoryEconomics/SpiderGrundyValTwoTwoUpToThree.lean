import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGrundyVal

/-!
# spider_grundy_val_two_two_up_to_three

Topic: combinatorial_games   Node: ffc4d4859b63

Provenance: helper lemma. arXiv:2610.15145, Corollary 5.7

For every natural number z with 1 ≤ z and z ≤ 3, the Grundy value spider_grundy_val 2 2 z of the spider tree S(2, 2, z) in the Game of Arrows is equal to z % 2.
-/

/-- The Grundy value of S(2, 2, z) equals z % 2 for all 1 ≤ z ≤ 3. -/
theorem spider_grundy_val_two_two_up_to_three (z : ℕ) (h1 : 1 ≤ z) (h3 : z ≤ 3) : spider_grundy_val 2 2 z = z % 2 := by
  interval_cases z <;> decide
