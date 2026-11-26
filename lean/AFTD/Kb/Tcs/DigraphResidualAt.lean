import AFTD.Prelude

/-!
# digraph_residual_at

Topic: graphs   Node: 0f3ad7e3afe9

Provenance: formalization of a published result. Source: arXiv:2611.32872 p. 3

For a finite type V with decidable equality, directed graphs G and H of type Digraph V with decidable adjacency relations, and a vertex v : V, digraph_residual_at G H v is the Finset of all vertices w : V such that for every vertex u : V, if u = v or G.Adj u v, then u = w or H.Adj u w.
-/

/-- The residual R_v = ⋂_{u ∈ N_G⁻[v]} N_H⁺[u] as a Finset of vertices w for digraphs G and H. -/
def digraph_residual_at {V : Type*} [Fintype V] [DecidableEq V]
    (G H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (v : V) : Finset V := Finset.univ.filter fun w => ∀ u, (u = v ∨ G.Adj u v) → (u = w ∨ H.Adj u w)
