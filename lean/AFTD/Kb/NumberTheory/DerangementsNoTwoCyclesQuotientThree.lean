import AFTD.Prelude
import AFTD.Kb.NumberTheory.DerangementsNoTwoCyclesQuotient
import AFTD.Kb.NumberTheory.DerangementsNoTwoCyclesCountThree
import AFTD.Kb.NumberTheory.DerangementsNoTwoCyclesCount

/-!
# derangements_no_two_cycles_quotient_three

Topic: elementary_number_theory   Node: 143ca357e984

Provenance: helper lemma. scout/2610-40342-a-p-adic-valuation-calculus-for-permutations-with-restricte.md:1608

The quotient derangements_no_two_cycles_quotient 3 equals 1.
-/

/-- The quotient Q_3 equals 1. -/
theorem derangements_no_two_cycles_quotient_three : derangements_no_two_cycles_quotient 3 = 1 := by
  simp [derangements_no_two_cycles_quotient, derangements_no_two_cycles_count_three]
