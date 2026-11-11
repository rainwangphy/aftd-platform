import AFTD.Prelude
import AFTD.Kb.Tcs.TenVertexExchangeGraph
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.TenVertexExchangeFamilyEq
import AFTD.Kb.Tcs.FiniteEdgePackingOddIncidenceBound
import AFTD.Kb.Tcs.TenVertexExchangeFiniteWitnessFacts
import AFTD.Kb.Tcs.TenVertexExchangeEdges
import AFTD.Kb.Tcs.TenVertexExchangeFamily
import AFTD.Kb.Tcs.TenVertexExchangePackingQ
import AFTD.Kb.Tcs.TenVertexExchangeTriangle
import AFTD.Kb.Tcs.TenVertexExchangePackingP

/-!
# ten_vertex_exchange_packing_upper

Topic: graphs   Node: 0140a1716da5

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

The witness has no packing of eleven edge-disjoint triangles.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace In732Upper
theorem in732_triangle_data :
    ∀ t ∈ ten_vertex_exchange_family, t ⊆ ten_vertex_exchange_edges ∧ t.card = 3 := by
  intro t ht
  simp only [ten_vertex_exchange_family, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst t <;> decide

theorem in732_incidence_data :
    ∀ v : Fin 10, ∀ t ∈ ten_vertex_exchange_family, Even ((t.filter (fun e => v ∈ e)).card) := by
  intro v t ht
  simp only [ten_vertex_exchange_family, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst t <;> fin_cases v <;> decide

theorem in732_odd_data :
    ∀ v ∈ ({0,4,5,6,7,8} : Finset (Fin 10)), Odd ((ten_vertex_exchange_edges.filter (fun e => v ∈ e)).card) := by decide

end In732Upper
open In732Upper

theorem ten_vertex_exchange_packing_upper : ∀ R : Finset (Finset (Sym2 (Fin 10))), R ⊆ simple_graph_triangle_edge_family ten_vertex_exchange_graph → (R : Set (Finset (Sym2 (Fin 10)))).Pairwise Disjoint → R.card ≤ 10 := by
  intro R hR hdisj
  have hF := ten_vertex_exchange_family_eq
  have hRF : R ⊆ ten_vertex_exchange_family := by simpa only [hF] using hR
  have hb := finite_edge_packing_odd_incidence_bound ten_vertex_exchange_edges R ({0,4,5,6,7,8} : Finset (Fin 10))
    (fun t ht => (in732_triangle_data t (hRF ht)).1) hdisj
    (fun t ht => (in732_triangle_data t (hRF ht)).2)
    (fun v t ht => in732_incidence_data v t (hRF ht)) in732_odd_data
  have hE : ten_vertex_exchange_edges.card = 35 := ten_vertex_exchange_finite_witness_facts.1
  have hO : ({0,4,5,6,7,8} : Finset (Fin 10)).card = 6 := by decide
  rw [hE,hO] at hb
  omega
