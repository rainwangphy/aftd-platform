import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetFiberFamily
import AFTD.Kb.Tcs.FinsetRestrictedFamilyEmpty
import AFTD.Kb.Tcs.FinsetRestrictedFamily

/-!
# finset_fiber_family_empty

Topic: combinatorics   Node: 0fc3f468d6cd

Provenance: helper lemma. arXiv:2611.06860, Section 2.2

The fiber family of the empty family is empty.
-/

/-- The fiber family of the empty family is empty. -/
theorem finset_fiber_family_empty {α : Type*} [Fintype α] [DecidableEq α] (J S : Finset α) : finset_fiber_family (∅ : Finset (Finset α)) J S = ∅ := by
  simp only [finset_fiber_family, finset_restricted_family_empty]
  apply Finset.filter_false_of_mem
  intro U _ hS
  exact Finset.not_nonempty_empty hS.nonempty
