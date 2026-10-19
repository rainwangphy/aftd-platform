import AFTD.Prelude
import AFTD.Kb.Tcs.IsSustainableTree
import AFTD.Kb.Tcs.IsGeneralizedTreeShift

/-!
# sustainable_gts_step

Topic: graphs   Node: 3232cc4fb346

Provenance: formalization of a published result. Source: arXiv:2610.17078 Open Problem 6.1

A transition step between two sustainable trees T and T' on a finite type V where T' is obtained from T by a generalized tree shift.
-/

/-- A single step of generalized tree shift between two sustainable trees. -/
def sustainable_gts_step {V : Type*} [Fintype V] [DecidableEq V] (T T' : SimpleGraph V) : Prop := is_sustainable_tree T ∧ is_sustainable_tree T' ∧ is_generalized_tree_shift T T'
