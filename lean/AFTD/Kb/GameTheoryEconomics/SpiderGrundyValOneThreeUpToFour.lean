import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGrundyVal
import AFTD.Kb.GameTheoryEconomics.SpiderGrundyValOneThreeUpToThree

/-!
# spider_grundy_val_one_three_up_to_four

Topic: combinatorial_games   Node: be8d558ed82c

Provenance: helper lemma. arXiv:2610.15145, Conjecture 7.4

For every natural number z with 1 ≤ z and z ≤ 4, the Grundy value spider_grundy_val 1 3 z of the spider tree S(1, 3, z) in the Game of Arrows is equal to z % 2.
-/

/-- The Grundy value of S(1, 3, z) equals z % 2 for all 1 ≤ z ≤ 4. -/
theorem spider_grundy_val_one_three_up_to_four (z : ℕ) (h1 : 1 ≤ z) (h4 : z ≤ 4) : spider_grundy_val 1 3 z = z % 2 := by
  rcases eq_or_lt_of_le h4 with rfl | h3
  · decide
  · exact spider_grundy_val_one_three_up_to_three z h1 (Nat.le_of_lt_succ h3)
