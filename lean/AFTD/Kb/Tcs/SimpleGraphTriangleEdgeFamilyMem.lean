import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily

/-!
# simple_graph_triangle_edge_family_mem

Topic: graphs   Node: 2c74f41c89b0

Provenance: helper lemma. step towards simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample

A set of three edges belongs to the triangle edge family of G iff it is the set of non-diagonal pairs spanned by some three vertices forming a triangle of G.
-/

/-- Membership in the triangle edge family: a three-edge set is the edge set of a triangle iff it is the non-diagonal pair set of some 3-clique. -/
theorem simple_graph_triangle_edge_family_mem {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (t : Finset (Sym2 V)) :
    t ∈ simple_graph_triangle_edge_family G ↔
      ∃ x : Finset V, G.IsNClique 3 x ∧ finite_vertex_set_edge_encoding x = t := by
  classical
  simp only [simple_graph_triangle_edge_family, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
