import AFTD.Prelude
import AFTD.Kb.Tcs.IsAdmissible

/-!
# isAdmissible_empty

Topic: combinatorics   Node: c7470029396f

Provenance: helper lemma. arXiv:2610.34372, text following Definition 1.1

The empty set is an admissible set of natural numbers.
-/

/-- The empty set of natural numbers is admissible. -/
theorem isAdmissible_empty : IsAdmissible ∅ := by
  intro B C hB hC _
  rw [Finset.subset_empty] at hB hC
  rw [hB, hC]
