import AFTD.Prelude
import AFTD.Kb.NumberTheory.DerangementsNoTwoCyclesCount

/-!
# derangements_no_two_cycles_count_three

Topic: elementary_number_theory   Node: b09f926c1c34

Provenance: helper lemma. scout/2610-40342-a-p-adic-valuation-calculus-for-permutations-with-restricte.md:1608

The number of derangements without 2-cycles of a 3-element set equals 2.
-/

/-- The number of derangements of Fin 3 with no 2-cycles is 2. -/
theorem derangements_no_two_cycles_count_three : derangements_no_two_cycles_count 3 = 2 := by
  decide
