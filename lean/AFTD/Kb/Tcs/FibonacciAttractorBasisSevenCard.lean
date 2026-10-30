import AFTD.Prelude
import AFTD.Kb.Tcs.FibonacciAttractorBasis

/-!
# fibonacci_attractor_basis_seven_card

Topic: combinatorics   Node: df1d05ffb98e

Provenance: helper lemma. arXiv:2610.10950 Smallest String Attractors and Minimal Coverage Certificates of Thue--Morse Words

The cardinality of the candidate attractor basis fibonacci_attractor_basis 7 is exactly 7.
-/

/-- The candidate basis B_7 has cardinality 7, matching ceil(3*7/2) - 4. -/
theorem fibonacci_attractor_basis_seven_card :
    (fibonacci_attractor_basis 7).card = 7 := by
  decide
