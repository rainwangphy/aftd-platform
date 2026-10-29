import AFTD.Prelude
import AFTD.Kb.Tcs.CoronaK1
import AFTD.Kb.Tcs.EdgeGeodesicTransversalNumber
import AFTD.Kb.Tcs.CoronaK1ExistsEdgeGeodesicTransversal
import AFTD.Kb.Tcs.IsEdgeGeodesicTransversal

/-!
# edge_geodesic_transversal_number_corona_k1_le

Topic: graphs   Node: fd8c35a354d3

Provenance: formalization of a published result. Source: arXiv:2610.36821 Section 5 (The Edge Geodesic Transversal Problem)

For every finite type V with 2 ≤ Fintype.card V and every connected simple graph G on V, the edge geodesic transversal number of the corona product corona_k1 G satisfies edge_geodesic_transversal_number (corona_k1 G) ≤ Fintype.card V - 1.
-/

/-- The edge geodesic transversal number of G ⊙ K_1 is at most |V| - 1. -/
theorem edge_geodesic_transversal_number_corona_k1_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    edge_geodesic_transversal_number (corona_k1 G) ≤ Fintype.card V - 1 := by
  obtain ⟨S, hS, hcard⟩ := corona_k1_exists_edge_geodesic_transversal G hG hn
  exact Nat.sInf_le ⟨S, hS, hcard⟩
