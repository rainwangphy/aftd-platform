import AFTD.Prelude

/-!
# graph_edge_boundary

Topic: graphs   Node: eb86981015d8

Provenance: formalization of a published result. Source: arXiv:2611.05034 Lemma 4.1

The edge boundary ∂_H S of a subset S ⊆ U in the induced subgraph H = G[U] is the finset of edges of G with one endpoint in S and one endpoint in U \ S.
-/

open scoped Classical in
/-- The edge boundary of a subset S ⊆ U in the induced subgraph G[U], consisting of edges with one endpoint in S and one in U \ S. -/
noncomputable def graph_edge_boundary {V : Type*} [Fintype V] (G : SimpleGraph V) (U S : Finset V) : Finset (Sym2 V) := G.edgeFinset.filter fun e => ∃ u ∈ S, ∃ v ∈ U \ S, e = s(u, v)
