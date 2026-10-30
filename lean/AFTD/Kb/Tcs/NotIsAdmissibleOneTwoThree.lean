import AFTD.Prelude
import AFTD.Kb.Tcs.IsAdmissible

/-!
# not_isAdmissible_one_two_three

Topic: combinatorics   Node: 117fd1e15858

Provenance: helper lemma. arXiv:2610.34372, Definition 1.1

The set {1, 2, 3} is not an admissible set of natural numbers.
-/

/-- The set {1, 2, 3} is not admissible because {1, 2} and {3} have the same sum 3 but different cardinalities. -/
theorem not_isAdmissible_one_two_three : ¬ IsAdmissible {1, 2, 3} := by
  intro h
  have hB : ({1, 2} : Finset ℕ) ⊆ {1, 2, 3} := by decide
  have hC : ({3} : Finset ℕ) ⊆ {1, 2, 3} := by decide
  have hsum : ({1, 2} : Finset ℕ).sum id = ({3} : Finset ℕ).sum id := by decide
  have hcard := h {1, 2} {3} hB hC hsum
  revert hcard
  decide
