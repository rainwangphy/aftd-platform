import AFTD.Prelude
import AFTD.Kb.Tcs.IsMaximalGeodesic
import AFTD.Kb.Tcs.EdgeGeodesicTransversalNumber
import AFTD.Kb.Tcs.IsEdgeGeodesicTransversal

/-!
# edge_cut_transversal_theorem

Topic: graphs   Node: 2c5950154c2a

Provenance: formalization of a published result. Source: arXiv:2610.36821 Theorem 5

Let G be a connected simple graph. Let S be a finite set of edges of G of cardinality k that is an edge cut induced by a vertex subset X (meaning there exists X : Set V such that for all e, e ∈ S ↔ e ∈ G.edgeSet ∧ ∃ u ∈ X, ∃ v ∉ X, e = s(u, v)), such that the number of connected components of G after deleting the edges in S is 2 (Nat.card of the connected components of G.deleteEdges S is 2). If for all vertices u, v and every walk p from u to v in G such that is_maximal_geodesic p, there exists a unique edge e such that e ∈ S ∧ e ∈ p.edges, and G contains k mutually edge-disjoint maximal geodesics (meaning there exist endpoints u, v : Fin k → V and walks P : (i : Fin k) → G.Walk (u i) (v i) such that each P i is a maximal geodesic and for all i ≠ j, any edge in P i does not belong to P j), then the edge geodesic transversal number of G equals the cardinality of S.
-/

/-- Theorem 5 (Edge-cut transversal theorem) of arXiv:2610.36821. -/
theorem edge_cut_transversal_theorem {V : Type*} (G : SimpleGraph V) (hG : G.Connected)
    (S : Finset (Sym2 V)) (k : ℕ) (hk : S.card = k)
    (hcut : ∃ X : Set V, ∀ e, e ∈ S ↔ e ∈ G.edgeSet ∧ ∃ u ∈ X, ∃ v ∉ X, e = s(u, v))
    (_hconn : Nat.card (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent = 2)
    (h_inter : ∀ ⦃u v : V⦄ (p : G.Walk u v), is_maximal_geodesic p → ∃! e, e ∈ S ∧ e ∈ p.edges)
    (h_disj : ∃ (u v : Fin k → V) (P : (i : Fin k) → G.Walk (u i) (v i)),
      (∀ i, is_maximal_geodesic (P i)) ∧
      ∀ (i j : Fin k), i ≠ j → ∀ e ∈ (P i).edges, e ∉ (P j).edges) :
    edge_geodesic_transversal_number G = S.card := by
  have _ := hG
  have hS_trans : is_edge_geodesic_transversal G S := by
    constructor
    · intro e he
      rcases hcut with ⟨X, hX⟩
      exact ((hX e).mp he).1
    · intro u v p hp
      have hp_max : is_maximal_geodesic p := by
        dsimp [is_maximal_geodesic]
        tauto
      rcases h_inter p hp_max with ⟨e, ⟨heS, he_p⟩, _⟩
      exact ⟨e, heS, he_p⟩
  have h_le : edge_geodesic_transversal_number G ≤ S.card := by
    dsimp [edge_geodesic_transversal_number]
    apply Nat.sInf_le
    exact ⟨S, hS_trans, rfl⟩
  have h_ge : S.card ≤ edge_geodesic_transversal_number G := by
    rw [hk]
    dsimp [edge_geodesic_transversal_number]
    apply le_csInf
    · exact ⟨S.card, ⟨S, hS_trans, rfl⟩⟩
    · rintro b ⟨T, hT, rfl⟩
      rcases h_disj with ⟨u, v, P, hP_max, hP_disj⟩
      have h_exists_e : ∀ i : Fin k, ∃ e ∈ T, e ∈ (P i).edges := by
        intro i
        have hp_geom : (P i).IsPath ∧ (P i).length = G.dist (u i) (v i) ∧
            (∀ w, G.Adj w (u i) → G.dist w (v i) ≤ (P i).length) ∧
            (∀ w, G.Adj (v i) w → G.dist (u i) w ≤ (P i).length) := by
          have := hP_max i
          dsimp [is_maximal_geodesic] at this
          tauto
        exact hT.2 (P i) hp_geom
      choose f hfT hfP using h_exists_e
      have h_inj : Set.InjOn f (Finset.univ : Finset (Fin k)) := by
        intros i _ j _ hij
        by_contra hne
        have := hP_disj i j hne (f i) (hfP i)
        rw [hij] at this
        exact this (hfP j)
      have h_maps : Set.MapsTo f (Finset.univ : Finset (Fin k)) T := by
        intros i _
        exact hfT i
      have h_card := Finset.card_le_card_of_injOn f h_maps h_inj
      simpa using h_card
  exact le_antisymm h_le h_ge
