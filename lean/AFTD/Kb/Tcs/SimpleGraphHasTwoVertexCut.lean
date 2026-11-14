import AFTD.Prelude

/-!
# simple_graph_has_two_vertex_cut

Topic: graphs   Node: 934c1e84038c

Provenance: formalization of a published result. Source: arXiv:2611.16649 Sec. 1, p. 1

A graph G has a 2-vertex cut if there exist two distinct vertices u, v : V such that the subgraph of G induced on the complement of {u, v} is not preconnected.
-/

/-- A simple graph has a 2-vertex cut if there exist two distinct vertices whose deletion leaves a non-preconnected induced subgraph. -/
def simple_graph_has_two_vertex_cut {V : Type*} (G : SimpleGraph V) : Prop := ∃ u v : V, u ≠ v ∧ ¬ (G.induce ({u, v}ᶜ)).Preconnected
