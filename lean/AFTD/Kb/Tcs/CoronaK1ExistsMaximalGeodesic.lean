import AFTD.Prelude
import AFTD.Kb.Tcs.CoronaK1
import AFTD.Kb.Tcs.IsMaximalGeodesic
import AFTD.Kb.Tcs.CoronaK1MaximalGeodesicEndpoints
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# corona_k1_exists_maximal_geodesic

Topic: graphs   Node: 1181dada425e

Provenance: helper lemma. step towards edge_geodesic_transversal_number_corona_k1_card_two

For every finite type V with 2 ≤ Fintype.card V and every connected simple graph G on V, there exist vertices x, y : V ⊕ V and a walk p between them in corona_k1 G such that is_maximal_geodesic p.
-/

/-- For every finite type V with 2 ≤ Fintype.card V and every connected simple graph G on V, there exist vertices x, y in the corona product corona_k1 G and a walk between them that is a maximal geodesic. -/
theorem corona_k1_exists_maximal_geodesic
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    ∃ (x y : V ⊕ V) (p : (corona_k1 G).Walk x y), is_maximal_geodesic p := by
  obtain ⟨u, v, huv⟩ := Fintype.one_lt_card_iff.mp hn
  have h_reach_G : G.Reachable u v := hG u v
  have h1 : (corona_k1 G).Adj (Sum.inr u) (Sum.inl u) := rfl
  have h2 : (corona_k1 G).Reachable (Sum.inl u) (Sum.inl v) :=
    SimpleGraph.Reachable.map ⟨Sum.inl, fun h => h⟩ h_reach_G
  have h3 : (corona_k1 G).Adj (Sum.inl v) (Sum.inr v) := rfl
  have h_reach : (corona_k1 G).Reachable (Sum.inr u) (Sum.inr v) := (h1.reachable.trans h2).trans h3.reachable
  obtain ⟨p, hp_len⟩ := h_reach.exists_walk_length_eq_dist
  have hp_path : p.IsPath := SimpleGraph.Walk.isPath_of_length_eq_dist p hp_len
  refine ⟨Sum.inr u, Sum.inr v, p, ?_⟩
  dsimp [is_maximal_geodesic]
  refine ⟨⟨hp_path, hp_len⟩, ?_, ?_⟩
  · intro w hw
    have hw' : (corona_k1 G).Adj (Sum.inr u) w := hw.symm
    have hw_eq : w = Sum.inl u := corona_k1_maximal_geodesic_endpoints_adj_inr_inv G u hw'
    subst hw_eq
    have hy_ne : (Sum.inr v : V ⊕ V) ≠ Sum.inr u := by
      intro h
      injection h with h'
      exact huv.symm h'
    have h_le := corona_k1_maximal_geodesic_endpoints_walk_from_inr_length_le G u (Sum.inr v) p hy_ne
    omega
  · intro w hw
    have hw_eq : w = Sum.inl v := corona_k1_maximal_geodesic_endpoints_adj_inr_inv G v hw
    subst hw_eq
    have hy_ne : (Sum.inr u : V ⊕ V) ≠ Sum.inr v := by
      intro h
      injection h with h'
      exact huv h'
    have h_le := corona_k1_maximal_geodesic_endpoints_walk_from_inr_length_le G v (Sum.inr u) p.reverse hy_ne
    rw [SimpleGraph.dist_comm]
    rw [SimpleGraph.Walk.length_reverse] at h_le
    omega
