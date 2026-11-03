import AFTD.Prelude

/-!
# simple_graph_ramsey_three_k_of_degree_ge

Topic: combinatorics   Node: b9121a6022f1

Provenance: helper lemma. step towards simple_graph_ramsey_three_ten_forty

In any finite simple graph, if a vertex has degree at least k, then either the graph contains a triangle or it contains an independent set of size k (a k-clique of its complement).
-/

/-- In any finite simple graph, if a vertex has degree at least k, then either the graph contains a triangle or an independent set of size k. -/
theorem simple_graph_ramsey_three_k_of_degree_ge {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] {k : ℕ} (v : α) (hdeg : k ≤ G.degree v) :
    ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree k := by
  by_cases h3 : G.CliqueFree 3
  · right
    intro hk
    have hindep : G.IsIndepSet (G.neighborSet v) := G.isIndepSet_neighborSet_of_triangleFree h3 v
    have hcard : k ≤ (G.neighborFinset v).card := by
      rwa [G.card_neighborFinset_eq_degree]
    obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq hcard
    have hs_indep : G.IsIndepSet (s : Set α) := by
      rw [← G.coe_neighborFinset] at hindep
      exact hindep.mono (Finset.coe_subset.mpr hs_sub)
    have hs_nclique : Gᶜ.IsNClique k s := by
      rw [SimpleGraph.isNClique_compl]
      exact ⟨hs_indep, hs_card⟩
    exact hk s hs_nclique
  · left
    exact h3
