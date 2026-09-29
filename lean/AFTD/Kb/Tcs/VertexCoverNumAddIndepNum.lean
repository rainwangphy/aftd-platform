import AFTD.Prelude

/-!
# vertex_cover_num_add_indep_num

Topic: graphs   Node: cea1059b8530

In any finite simple graph G, the sum of the vertex cover number and the independence number is equal to the number of vertices.
-/

/-- Gallai's identity: the sum of the vertex cover number and the independence number equals the vertex count. -/
theorem vertex_cover_num_add_indep_num {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.vertexCoverNum + G.indepNum = Fintype.card V := by
  classical
  apply le_antisymm
  · obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
    have h_vc : G.IsVertexCover (s : Set V)ᶜ := by
      rw [SimpleGraph.isVertexCover_compl]
      exact hs.isIndepSet
    have h1 : G.vertexCoverNum ≤ (s : Set V)ᶜ.encard := h_vc.vertexCoverNum_le
    have h2 : (s : Set V).encard = (G.indepNum : ℕ∞) := by
      rw [Set.encard_coe_eq_coe_finsetCard, hs.card_eq]
    have h3 : (s : Set V)ᶜ.encard + (s : Set V).encard = (Fintype.card V : ℕ∞) := by
      rw [add_comm, Set.encard_add_encard_compl, Set.encard_univ, ENat.card_eq_coe_fintype_card]
    rw [← h2, ← h3]
    gcongr
  · obtain ⟨c, hc_card, hc_vc⟩ := G.vertexCoverNum_exists
    have h_indep : G.IsIndepSet (cᶜ.toFinset : Set V) := by
      rwa [Set.coe_toFinset, SimpleGraph.isIndepSet_compl_iff_isVertexCover]
    have hs_card : (cᶜ.toFinset.card : ℕ∞) ≤ G.indepNum := by
      exact_mod_cast (h_indep.card_le_indepNum)
    have h_encard : cᶜ.encard = (cᶜ.toFinset.card : ℕ∞) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, Set.coe_toFinset]
    have h_univ : (Fintype.card V : ℕ∞) = c.encard + cᶜ.encard := by
      rw [Set.encard_add_encard_compl, Set.encard_univ, ENat.card_eq_coe_fintype_card]
    rw [h_univ, hc_card, h_encard]
    gcongr
