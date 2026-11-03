import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_triangle_edge_family

Topic: graphs   Node: 0c3088798f17

Provenance: helper lemma. Graph-to-set-family bridge for the triangle packing separator route.

The family of three-edge sets of all triangles of a finite simple graph.
-/

noncomputable def simple_graph_triangle_edge_family {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Finset (Finset (Sym2 V)) := by
  classical
  exact ((Finset.univ : Finset (Finset V)).filter (G.IsNClique 3)).image finite_vertex_set_edge_encoding
