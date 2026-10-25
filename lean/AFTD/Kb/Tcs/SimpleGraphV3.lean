import AFTD.Prelude

/-!
# simple_graph_V3

Topic: graphs   Node: 9124db138300

Provenance: formalization of a published result. Source: arXiv:2610.21868 Sec. 1

For a finite type V with decidable equality and a simple graph G on V with decidable adjacency, simple_graph_V3 G is the finset of all vertices v in V whose degree in G is equal to 3.
-/

/-- The finset of vertices of degree 3 in a finite simple graph. -/
def simple_graph_V3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 3)
