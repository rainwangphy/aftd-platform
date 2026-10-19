import AFTD.Prelude
import AFTD.Kb.Tcs.IsNonsustainableTree
import AFTD.Kb.Tcs.IsGeneralizedTreeShift

/-!
# nonsustainable_gts_step

Topic: graphs   Node: cb4f3e9bbd33

Provenance: formalization of a published result. Source: arXiv:2610.17078 Open Problem 6.1

A transition step between two non-sustainable trees T and T' on a finite type V where T' is obtained from T by a generalized tree shift.
-/

/-- A single step of generalized tree shift between two non-sustainable trees. -/
def nonsustainable_gts_step {V : Type*} [Fintype V] [DecidableEq V] (T T' : SimpleGraph V) : Prop := is_nonsustainable_tree T ∧ is_nonsustainable_tree T' ∧ is_generalized_tree_shift T T'
