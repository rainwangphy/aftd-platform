import AFTD.Prelude
import AFTD.Kb.NumberTheory.DerangementsNoTwoCyclesCount

/-!
# derangements_no_two_cycles_quotient

Topic: elementary_number_theory   Node: 0b2ac7ca8e93

Provenance: formalization of a published result. Source: scout/2610-40342-a-p-adic-valuation-calculus-for-permutations-with-restricte.md:1608

For a natural number n, derangements_no_two_cycles_quotient n is the quotient of the number of derangements of Fin n without 2-cycles divided by (n - 1) * (n - 2).
-/

/-- The quotient Q_n = T(n,2) / ((n-1)(n-2)) for column 2 of derangements without 2-cycles. -/
def derangements_no_two_cycles_quotient (n : ℕ) : ℕ := derangements_no_two_cycles_count n / ((n - 1) * (n - 2))
