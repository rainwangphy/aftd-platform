import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetRestrictedFamily
import AFTD.Kb.Tcs.OrientedOverlapMultiplicityBudget

/-!
# finset_restricted_family_empty

Topic: combinatorics   Node: 559f2e679c83

Provenance: helper lemma. arXiv:2611.06860, Section 2.2

The restricted family of the empty family is empty.
-/

/-- The restricted family of the empty family is empty. -/
theorem finset_restricted_family_empty {α : Type*} [DecidableEq α] (J U : Finset α) : finset_restricted_family (∅ : Finset (Finset α)) J U = ∅ := by first | exact oriented_overlap_multiplicity_budget | (apply oriented_overlap_multiplicity_budget <;> assumption) | (apply oriented_overlap_multiplicity_budget <;> simp_all) | simpa using oriented_overlap_multiplicity_budget | (simp only [finset_restricted_family] at *; first | exact oriented_overlap_multiplicity_budget | (apply oriented_overlap_multiplicity_budget <;> assumption) | (apply oriented_overlap_multiplicity_budget <;> simp_all) | simpa using oriented_overlap_multiplicity_budget)
