import AFTD.Prelude
import AFTD.Kb.Tcs.GeodesicTransversalNumber
import AFTD.Kb.Tcs.EdgeGeodesicTransversalNumber
import AFTD.Kb.Tcs.ExistsGeodesicTransversalOfEdgeGeodesicTransversal
import AFTD.Kb.Tcs.IsEdgeGeodesicTransversal
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.IsGeodesicTransversal
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# geodesic_transversal_number_le_edge_geodesic_transversal_number

Topic: graphs   Node: 6aea6cca3793

Provenance: formalization of a published result. Source: scout/2610-36821-the-edge-geodesic-transversal-problem.md:103

For any connected simple graph G that admits a finite edge geodesic transversal, the vertex geodesic transversal number of G is bounded above by the edge geodesic transversal number of G, that is, gt(G) ≤ gt_e(G).
-/

/-- For any connected simple graph G admitting a finite edge geodesic transversal, the vertex geodesic transversal number gt(G) is at most the edge geodesic transversal number gt_e(G). -/
theorem geodesic_transversal_number_le_edge_geodesic_transversal_number {V : Type*} (G : SimpleGraph V) (hG : G.Connected) (hT : ∃ T : Finset (Sym2 V), is_edge_geodesic_transversal G T) : geodesic_transversal_number G ≤ edge_geodesic_transversal_number G := by
  have _ := hG
  unfold edge_geodesic_transversal_number
  rcases hT with ⟨T0, hT0⟩
  have hne : { k : ℕ | ∃ S : Finset (Sym2 V), is_edge_geodesic_transversal G S ∧ S.card = k }.Nonempty := by
    exact ⟨T0.card, ⟨T0, hT0, rfl⟩⟩
  have hmem := Nat.sInf_mem hne
  dsimp at hmem
  rcases hmem with ⟨T, hT_trans, hT_card⟩
  rcases exists_geodesic_transversal_of_edge_geodesic_transversal G T hT_trans with ⟨S, hS_trans, hS_le⟩
  have hS_mem : S.card ∈ { k : ℕ | ∃ S' : Finset V, is_geodesic_transversal G S' ∧ S'.card = k } := by
    exact ⟨S, hS_trans, rfl⟩
  unfold geodesic_transversal_number
  have hle := Nat.sInf_le hS_mem
  linarith
