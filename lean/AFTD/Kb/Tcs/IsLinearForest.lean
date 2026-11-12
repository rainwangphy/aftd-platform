import AFTD.Prelude

/-!
# is_linear_forest

Topic: graphs   Node: 0b0e44ad95c6

Provenance: formalization of a published result. Source: arXiv:2611.12781 Section 1

A simple graph is a linear forest if it is acyclic and every vertex has at most two neighbors.
-/

/-- A simple graph is a linear forest if it is acyclic and every vertex has degree at most 2. -/
def is_linear_forest {V : Type*} (G : SimpleGraph V) : Prop := G.IsAcyclic ∧ ∀ v : V, (G.neighborSet v).encard ≤ 2
