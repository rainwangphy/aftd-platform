import AFTD.Prelude
import AFTD.Kb.Tcs.TenVertexExchangeEdges
import AFTD.Kb.Tcs.TenVertexExchangeFamily
import AFTD.Kb.Tcs.TenVertexExchangePackingP
import AFTD.Kb.Tcs.TenVertexExchangePackingQ
import AFTD.Kb.Tcs.TenVertexExchangeTriangle

/-!
# ten_vertex_exchange_finite_witness_facts

Topic: graphs   Node: 9659334240ec

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

The explicit edge and triangle lists have sizes 35 and 52; the displayed P and Q are edge-disjoint ten-triangle packings in the list, and Q has no fully singleton-forced triangle relative to that list.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem ten_vertex_exchange_finite_witness_facts :
    ten_vertex_exchange_edges.card = 35 ∧ ten_vertex_exchange_family.card = 52 ∧
    ten_vertex_exchange_packing_p.card = 10 ∧ ten_vertex_exchange_packing_q.card = 10 ∧
    ten_vertex_exchange_packing_p ⊆ ten_vertex_exchange_family ∧ ten_vertex_exchange_packing_q ⊆ ten_vertex_exchange_family ∧
    (ten_vertex_exchange_packing_p : Set (Finset (Sym2 (Fin 10)))).Pairwise Disjoint ∧
    (ten_vertex_exchange_packing_q : Set (Finset (Sym2 (Fin 10)))).Pairwise Disjoint ∧
    ∀ q ∈ ten_vertex_exchange_packing_q, ¬ q ⊆ ((ten_vertex_exchange_family.filter (fun t => (t ∩ ten_vertex_exchange_packing_q.biUnion id).card = 1)).biUnion id) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro q hq
  simp only [ten_vertex_exchange_packing_q, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with h | h | h | h | h | h | h | h | h | h <;> subst q <;> decide
