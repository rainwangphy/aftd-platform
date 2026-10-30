import AFTD.Prelude
import AFTD.Kb.Tcs.CoronaK1
import AFTD.Kb.Tcs.EdgeGeodesicTransversalNumber
import AFTD.Kb.Tcs.EdgeGeodesicTransversalNumberCoronaK1Le
import AFTD.Kb.Tcs.CoronaK1ExistsMaximalGeodesic
import AFTD.Kb.Tcs.IsMaximalGeodesic
import AFTD.Kb.Tcs.CoronaK1ExistsEdgeGeodesicTransversal
import AFTD.Kb.Tcs.IsEdgeGeodesicTransversal

/-!
# edge_geodesic_transversal_number_corona_k1_card_two

Topic: graphs   Node: e7d682b20f52

Provenance: helper lemma. arXiv:2610.36821 Section 5 (The Edge Geodesic Transversal Problem)

For every finite type V with Fintype.card V = 2 and every connected simple graph G on V, the edge geodesic transversal number of the corona product corona_k1 G satisfies edge_geodesic_transversal_number (corona_k1 G) = 1.
-/

/-- The edge geodesic transversal number of G ⊙ K_1 equals 1 when G has 2 vertices. -/
theorem edge_geodesic_transversal_number_corona_k1_card_two
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) (hn : Fintype.card V = 2) :
    edge_geodesic_transversal_number (corona_k1 G) = 1 := by
  have h2 : 2 ≤ Fintype.card V := by omega
  have h_le := edge_geodesic_transversal_number_corona_k1_le G hG h2
  rw [hn] at h_le
  have h_ge : 1 ≤ edge_geodesic_transversal_number (corona_k1 G) := by
    unfold edge_geodesic_transversal_number
    apply le_csInf
    · rcases corona_k1_exists_edge_geodesic_transversal G hG h2 with ⟨S, hS, -⟩
      exact ⟨S.card, S, hS, rfl⟩
    · rintro k ⟨S, hS, rfl⟩
      rcases corona_k1_exists_maximal_geodesic G hG h2 with ⟨x, y, p, hp⟩
      rcases hp with ⟨⟨hp1, hp2⟩, hp3, hp4⟩
      obtain ⟨e, heS, -⟩ := hS.2 p ⟨hp1, hp2, hp3, hp4⟩
      exact Finset.card_pos.mpr ⟨e, heS⟩
  omega
