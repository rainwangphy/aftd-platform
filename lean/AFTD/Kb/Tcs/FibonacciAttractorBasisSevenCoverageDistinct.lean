import AFTD.Prelude
import AFTD.Kb.Tcs.FibonacciAttractorBasis
import AFTD.Kb.Tcs.WordOccurrenceCoverage
import AFTD.Kb.Tcs.FibonacciWord

/-!
# fibonacci_attractor_basis_seven_coverage_distinct

Topic: combinatorics   Node: 5b3d1f0552fb

Provenance: helper lemma. arXiv:2610.10950 Smallest String Attractors and Minimal Coverage Certificates of Thue--Morse Words

The cardinality of the image under word_occurrence_coverage (fibonacci_word 7) of fibonacci_attractor_basis 7 is 7, showing that all 7 candidate basis words have distinct occurrence coverages in F_7.
-/

/-- The occurrence coverages of the 7 candidate basis words in B_7 are pairwise distinct in F_7. -/
theorem fibonacci_attractor_basis_seven_coverage_distinct :
    ((fibonacci_attractor_basis 7).image (word_occurrence_coverage (fibonacci_word 7))).card = 7 := by
  decide
