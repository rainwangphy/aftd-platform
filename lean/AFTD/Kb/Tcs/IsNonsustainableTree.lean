import AFTD.Prelude
import AFTD.Kb.Tcs.IsSustainableTree

/-!
# is_nonsustainable_tree

Topic: graphs   Node: 13ab41689a4b

Provenance: formalization of a published result. Source: arXiv:2610.17078 Section 1

A tree T is non-sustainable if T is a tree and T is not sustainable.
-/

/-- A tree is non-sustainable if it is a tree and not sustainable. -/
def is_nonsustainable_tree {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) : Prop := T.IsTree ∧ ¬ is_sustainable_tree T
