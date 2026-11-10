import AFTD.Prelude

/-!
# simple_graph_edge_conflict

Topic: graphs   Node: fa6c6eaae3a2

Provenance: formalization of a published result. Source: arXiv:2611.10883, Section 2

Two distinct edges e₁, e₂ ∈ G.edgeSet of a simple graph G conflict if they share an endpoint or are joined by an edge of G.
-/

/-- Two distinct edges in a graph conflict if they share an endpoint or are joined by an edge. -/
def simple_graph_edge_conflict {V : Type*} (G : SimpleGraph V) (e₁ e₂ : G.edgeSet) : Prop := e₁ ≠ e₂ ∧ ∃ u ∈ (e₁ : Sym2 V), ∃ v ∈ (e₂ : Sym2 V), u = v ∨ G.Adj u v
