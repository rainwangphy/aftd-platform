import AFTD.Prelude

/-!
# minor_edge_is_loop

Topic: graphs   Node: 871fe1f3a58d

Provenance: formalization of a published result. Source: arXiv:2610.40844 Section 2.1

For a simple graph G and a partial edge-weight realization β : G.edgeSet → Option Bool, an edge e of G is a loop in the minor G_β (obtained by contracting edges with weight 0 and deleting edges with weight 1) if its endpoints are connected by a path in the subgraph of contracted edges (weight 0).
-/

open scoped Classical in
/-- An edge of G is a loop in the minor G_β if its endpoints are connected by edges with weight 0 (contracted edges). -/
def minor_edge_is_loop {V : Type*} (G : SimpleGraph V) (β : G.edgeSet → Option Bool)
    (e : G.edgeSet) : Prop := ∃ u v : V, (e : Sym2 V) = s(u, v) ∧
    (SimpleGraph.fromEdgeSet {s | ∃ h : s ∈ G.edgeSet, β ⟨s, h⟩ = some false}).Reachable u v
