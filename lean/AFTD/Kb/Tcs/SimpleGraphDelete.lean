import AFTD.Prelude

/-!
# SimpleGraph.delete

Topic: graphs   Node: 2f694b8e504b

Provenance: formalization of a published result. Source: arXiv:2611.12781 Property 2.3

For a simple graph G on vertex type V and a vertex u : V, SimpleGraph.delete G u is the induced subgraph G.induce (Set.univ \ {u}) on the subtype ↑(Set.univ \ {u} : Set V).
-/

/-- The induced subgraph of G obtained by deleting vertex u. -/
def SimpleGraph.delete {V : Type*} (G : SimpleGraph V) (u : V) : SimpleGraph ↑(Set.univ \ {u} : Set V) := G.induce (Set.univ \ {u})
