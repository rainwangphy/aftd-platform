import AFTD.Prelude

/-!
# simple_graph_ramsey_three_ten_forty_outer_indep_lift

Topic: combinatorics   Node: a92e26ea553d

Provenance: helper lemma. step towards simple_graph_ramsey_three_ten_forty_of_max_degree_le_nine

If I is an independent set of at least 9 vertices of a simple graph G, and v is a vertex outside I that is adjacent to no vertex of I, then G has an independent set of 10 vertices; equivalently the complement of G is not 10-clique-free.
-/

/-- Lifting an outer independent set of size ≥ 9 by a non-adjacent vertex v gives an independent 10-set; hence the complement is not 10-clique-free. -/
theorem simple_graph_ramsey_three_ten_forty_outer_indep_lift {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) {v : α} {I : Finset α}
    (hI : G.IsIndepSet (I : Set α)) (hv : v ∉ I)
    (hne : ∀ x ∈ I, ¬ G.Adj v x) (hcard : 9 ≤ I.card) :
    ¬ Gᶜ.CliqueFree 10 := by
  intro hcf
  set J : Finset α := insert v I with hJ
  have hJind : G.IsIndepSet (J : Set α) := by
    rw [SimpleGraph.isIndepSet_iff] at hI ⊢
    rw [hJ, Finset.coe_insert, Set.pairwise_insert]
    refine ⟨hI, ?_⟩
    intro b hb _
    rw [Finset.mem_coe] at hb
    exact ⟨hne b hb, fun h => hne b hb ((G.adj_comm b v).mp h)⟩
  have hJcard : 10 ≤ J.card := by
    rw [hJ, Finset.card_insert_of_notMem hv]
    omega
  obtain ⟨t, htJ, htcard⟩ := Finset.exists_subset_card_eq hJcard
  have htind : G.IsIndepSet (t : Set α) := by
    rw [SimpleGraph.isIndepSet_iff] at hJind ⊢
    exact hJind.mono (by
      intro x hx
      exact Finset.mem_coe.mpr (htJ (Finset.mem_coe.mp hx)))
  have hncl : Gᶜ.IsNClique 10 t := by
    rw [SimpleGraph.isNClique_compl, SimpleGraph.isNIndepSet_iff]
    exact ⟨htind, htcard⟩
  exact (SimpleGraph.IsNClique.not_cliqueFree hncl) hcf
