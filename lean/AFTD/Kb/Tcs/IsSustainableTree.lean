import AFTD.Prelude
import AFTD.Kb.Tcs.IsSustainableEdge

/-!
# is_sustainable_tree

Topic: graphs   Node: c23cd937ef05

Provenance: formalization of a published result. Source: arXiv:2610.17078 Section 1

A tree T is sustainable if every edge of T is sustainable.
-/

/-- A tree is sustainable if every edge in it is sustainable. -/
def is_sustainable_tree {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) : Prop := T.IsTree ∧ ∀ e ∈ T.edgeSet, is_sustainable_edge T e
