import AFTD.Prelude

/-!
# is_bridgeless_graph

Topic: graphs   Node: 441da6e7d890

Provenance: formalization of a published result. Source: arXiv:2610.09648 Section 1

A simple graph G is bridgeless if no edge of G is a bridge.
-/

/-- A simple graph G is bridgeless if no edge of G is a bridge. -/
def is_bridgeless_graph {V : Type*} (G : SimpleGraph V) : Prop := ∀ e ∈ G.edgeSet, ¬ G.IsBridge e
