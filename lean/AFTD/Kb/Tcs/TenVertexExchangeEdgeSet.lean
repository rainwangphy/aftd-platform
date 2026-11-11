import AFTD.Prelude
import AFTD.Kb.Tcs.TenVertexExchangeGraph
import AFTD.Kb.Tcs.TenVertexExchangeEdges
import AFTD.Kb.Tcs.TenVertexExchangeFiniteWitnessFacts
import AFTD.Kb.Tcs.TenVertexExchangePackingQ
import AFTD.Kb.Tcs.TenVertexExchangeFamily
import AFTD.Kb.Tcs.TenVertexExchangePackingP

/-!
# ten_vertex_exchange_edge_set

Topic: graphs   Node: ca0178b4dee3

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

The witness graph has exactly the 35 listed edges.
-/

theorem ten_vertex_exchange_edge_set : (↑ten_vertex_exchange_edges : Set (Sym2 (Fin 10))) = ten_vertex_exchange_graph.edgeSet ∧ ten_vertex_exchange_edges.card = 35 := by
  refine ⟨?_, ten_vertex_exchange_finite_witness_facts.1⟩
  unfold ten_vertex_exchange_graph
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext x
  simp only [SetLike.mem_coe, Set.mem_sdiff, Sym2.mem_diagSet, iff_self_and]
  have hdiag : ∀ y ∈ ten_vertex_exchange_edges, ¬y.IsDiag := by decide
  exact hdiag x
