import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCyclePermsCount

/-!
# derangements_no_two_cycles_count

Topic: elementary_number_theory   Node: 9de1b3fa7030

Provenance: formalization of a published result. Source: scout/2610-40342-a-p-adic-valuation-calculus-for-permutations-with-restricte.md:1608

For a natural number n, derangements_no_two_cycles_count n is the number of permutations of Fin n that have no cycles of length 1 and no cycles of length 2.
-/

/-- Number of derangements of Fin n having no 2-cycles, i.e. permutations avoiding cycle lengths 1 and 2. -/
def derangements_no_two_cycles_count (n : ℕ) : ℕ := restricted_cycle_perms_count n {1, 2}
