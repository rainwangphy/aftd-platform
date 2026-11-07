import AFTD.Prelude

/-!
# minor_edge_is_bridge

Topic: graphs   Node: 6f4ee83b1c77

Provenance: formalization of a published result. Source: arXiv:2610.40844 Section 2.1

For a simple graph G and a partial edge-weight realization β : G.edgeSet → Option Bool, an edge e of G is a bridge in the minor G_β if it is not a loop and removing e along with all deleted edges (weight 1) disconnects its endpoints in G.
-/

open scoped Classical in
/-- An edge of G is a bridge in the minor G_β if it is not a loop and removing it together with weight-1 edges disconnects its endpoints. -/
def minor_edge_is_bridge {V : Type*} (G : SimpleGraph V) (β : G.edgeSet → Option Bool)
    (e : G.edgeSet) : Prop := ∃ u v : V, (e : Sym2 V) = s(u, v) ∧
    ¬ (SimpleGraph.fromEdgeSet {s | ∃ h : s ∈ G.edgeSet, β ⟨s, h⟩ = some false}).Reachable u v ∧
    ¬ (G.deleteEdges (insert (e : Sym2 V) {s | ∃ h : s ∈ G.edgeSet, β ⟨s, h⟩ = some true})).Reachable u v
