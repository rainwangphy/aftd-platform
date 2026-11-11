import AFTD.Prelude
import AFTD.Kb.Tcs.TenVertexExchangeGraph
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.TenVertexExchangeFamilyEq
import AFTD.Kb.Tcs.TenVertexExchangeEdgeSet
import AFTD.Kb.Tcs.TenVertexExchangePackingQ
import AFTD.Kb.Tcs.TenVertexExchangeFamily
import AFTD.Kb.Tcs.TenVertexExchangeTriangle
import AFTD.Kb.Tcs.TenVertexExchangeEdges
import AFTD.Kb.Tcs.TenVertexExchangePackingP

/-!
# ten_vertex_exchange_edge_avoidable

Topic: graphs   Node: 03673e0cd58b

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

For each of the 35 edges, a ten-triangle packing avoids that edge.
-/

def ten_vertex_exchange_edge_avoidable_packings : List (Finset (Finset (Sym2 (Fin 10)))) := [
  ten_vertex_exchange_packing_q,
  {ten_vertex_exchange_triangle 0 1 3, ten_vertex_exchange_triangle 0 2 8, ten_vertex_exchange_triangle 0 6 7, ten_vertex_exchange_triangle 1 2 7, ten_vertex_exchange_triangle 4 6 8, ten_vertex_exchange_triangle 3 4 7, ten_vertex_exchange_triangle 1 4 5, ten_vertex_exchange_triangle 5 8 9, ten_vertex_exchange_triangle 2 3 9, ten_vertex_exchange_triangle 3 5 6},
  {ten_vertex_exchange_triangle 0 1 3, ten_vertex_exchange_triangle 0 2 9, ten_vertex_exchange_triangle 0 7 8, ten_vertex_exchange_triangle 3 6 9, ten_vertex_exchange_triangle 4 6 8, ten_vertex_exchange_triangle 5 8 9, ten_vertex_exchange_triangle 2 3 7, ten_vertex_exchange_triangle 3 4 5, ten_vertex_exchange_triangle 1 2 5, ten_vertex_exchange_triangle 1 4 7},
  {ten_vertex_exchange_triangle 0 1 7, ten_vertex_exchange_triangle 2 8 9, ten_vertex_exchange_triangle 0 2 3, ten_vertex_exchange_triangle 0 6 9, ten_vertex_exchange_triangle 3 5 9, ten_vertex_exchange_triangle 1 2 5, ten_vertex_exchange_triangle 3 4 6, ten_vertex_exchange_triangle 2 4 7, ten_vertex_exchange_triangle 6 7 8, ten_vertex_exchange_triangle 4 5 8},
  {ten_vertex_exchange_triangle 0 1 7, ten_vertex_exchange_triangle 2 8 9, ten_vertex_exchange_triangle 0 3 9, ten_vertex_exchange_triangle 0 6 8, ten_vertex_exchange_triangle 5 6 9, ten_vertex_exchange_triangle 4 6 7, ten_vertex_exchange_triangle 4 5 8, ten_vertex_exchange_triangle 2 3 7, ten_vertex_exchange_triangle 1 2 4, ten_vertex_exchange_triangle 1 3 5},
  {ten_vertex_exchange_triangle 0 1 7, ten_vertex_exchange_triangle 0 2 8, ten_vertex_exchange_triangle 0 3 9, ten_vertex_exchange_triangle 2 5 9, ten_vertex_exchange_triangle 6 8 9, ten_vertex_exchange_triangle 4 5 6, ten_vertex_exchange_triangle 3 6 7, ten_vertex_exchange_triangle 4 7 8, ten_vertex_exchange_triangle 1 3 5, ten_vertex_exchange_triangle 1 2 4},
  {ten_vertex_exchange_triangle 0 1 7, ten_vertex_exchange_triangle 0 2 8, ten_vertex_exchange_triangle 0 3 9, ten_vertex_exchange_triangle 2 5 9, ten_vertex_exchange_triangle 6 8 9, ten_vertex_exchange_triangle 4 5 8, ten_vertex_exchange_triangle 3 5 6, ten_vertex_exchange_triangle 4 6 7, ten_vertex_exchange_triangle 2 3 7, ten_vertex_exchange_triangle 1 3 4},
  {ten_vertex_exchange_triangle 0 1 7, ten_vertex_exchange_triangle 0 2 8, ten_vertex_exchange_triangle 0 3 9, ten_vertex_exchange_triangle 1 2 5, ten_vertex_exchange_triangle 4 5 8, ten_vertex_exchange_triangle 6 8 9, ten_vertex_exchange_triangle 3 5 6, ten_vertex_exchange_triangle 4 6 7, ten_vertex_exchange_triangle 2 3 7, ten_vertex_exchange_triangle 1 3 4},
  {ten_vertex_exchange_triangle 0 1 7, ten_vertex_exchange_triangle 0 2 8, ten_vertex_exchange_triangle 0 6 9, ten_vertex_exchange_triangle 5 8 9, ten_vertex_exchange_triangle 2 3 9, ten_vertex_exchange_triangle 1 2 5, ten_vertex_exchange_triangle 1 3 4, ten_vertex_exchange_triangle 3 6 7, ten_vertex_exchange_triangle 4 5 6, ten_vertex_exchange_triangle 4 7 8},
  {ten_vertex_exchange_triangle 0 1 7, ten_vertex_exchange_triangle 0 2 9, ten_vertex_exchange_triangle 3 4 6, ten_vertex_exchange_triangle 0 6 8, ten_vertex_exchange_triangle 5 6 9, ten_vertex_exchange_triangle 4 7 8, ten_vertex_exchange_triangle 2 3 7, ten_vertex_exchange_triangle 1 3 5, ten_vertex_exchange_triangle 1 2 4, ten_vertex_exchange_triangle 2 5 8},
  ten_vertex_exchange_packing_p
]

lemma ten_vertex_exchange_edge_avoidable_packings_valid :
    ∀ R ∈ ten_vertex_exchange_edge_avoidable_packings,
      R ⊆ ten_vertex_exchange_family ∧ R.card = 10 ∧ (R : Set (Finset (Sym2 (Fin 10)))).Pairwise Disjoint := by
  intro R hR
  simp only [ten_vertex_exchange_edge_avoidable_packings, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma ten_vertex_exchange_edge_avoidable_check :
    ∀ e ∈ ten_vertex_exchange_edges, ∃ R ∈ ten_vertex_exchange_edge_avoidable_packings, e ∉ R.biUnion id := by
  decide

theorem ten_vertex_exchange_edge_avoidable : ∀ e ∈ ten_vertex_exchange_graph.edgeSet, ∃ R : Finset (Finset (Sym2 (Fin 10))), R ⊆ simple_graph_triangle_edge_family ten_vertex_exchange_graph ∧ R.card = 10 ∧ (R : Set (Finset (Sym2 (Fin 10)))).Pairwise Disjoint ∧ e ∉ R.biUnion id := by
  intro e he
  have he_edges : e ∈ ten_vertex_exchange_edges := by
    have h := ten_vertex_exchange_edge_set.1.symm
    have he' : e ∈ (↑ten_vertex_exchange_edges : Set (Sym2 (Fin 10))) := h ▸ he
    exact Finset.mem_coe.mp he'
  obtain ⟨R, hR, heR⟩ := ten_vertex_exchange_edge_avoidable_check e he_edges
  obtain ⟨hsub, hcard, hdisj⟩ := ten_vertex_exchange_edge_avoidable_packings_valid R hR
  refine ⟨R, ?_, hcard, hdisj, heR⟩
  rw [ten_vertex_exchange_family_eq]
  exact hsub
