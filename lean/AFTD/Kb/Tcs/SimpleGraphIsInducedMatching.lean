import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEdgeConflict

/-!
# simple_graph_is_induced_matching

Topic: graphs   Node: 6cc55955d615

Provenance: formalization of a published result. Source: arXiv:2611.10883, Section 2

A set E of edges of a simple graph G is an induced matching if no two edges of E conflict in G.
-/

/-- A set of edges is an induced matching if no two of its edges conflict. -/
def simple_graph_is_induced_matching {V : Type*} (G : SimpleGraph V) (E : Set G.edgeSet) : Prop := ∀ ⦃e₁ e₂⦄, e₁ ∈ E → e₂ ∈ E → ¬ simple_graph_edge_conflict G e₁ e₂
