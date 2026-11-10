import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.FinsetFiberFamilyEmpty

/-!
# not_is_uncomplemented_pair_compl

Topic: combinatorics   Node: 1bcf377414e2

Provenance: helper lemma. folklore

The family consisting of a set and its complement is not uncomplemented.
-/

/-- A pair of a set and its complement is not uncomplemented. -/
lemma not_is_uncomplemented_pair_compl {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) : ¬ is_uncomplemented ({A, Aᶜ} : Finset (Finset α)) := by first | exact finset_fiber_family_empty | (apply finset_fiber_family_empty <;> assumption) | (apply finset_fiber_family_empty <;> simp_all) | simpa using finset_fiber_family_empty | (simp only [is_uncomplemented] at *; first | exact finset_fiber_family_empty | (apply finset_fiber_family_empty <;> assumption) | (apply finset_fiber_family_empty <;> simp_all) | simpa using finset_fiber_family_empty)
