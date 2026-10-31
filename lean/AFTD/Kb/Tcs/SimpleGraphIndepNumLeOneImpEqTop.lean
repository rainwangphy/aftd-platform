import AFTD.Prelude

/-!
# simple_graph_indepNum_le_one_imp_eq_top

Topic: graphs   Node: 884f97f7bea9

Provenance: helper lemma. step towards radius_independence_connectivity_hamiltonian_interpolation

If G is not the complete graph, there exist two distinct non-adjacent vertices, forming an independent set of size 2, so indepNum G >= 2. By contrapositive, indepNum G <= 1 implies G = ⊤.
-/

/-- Every finite simple graph with independence number at most 1 is the complete graph. -/
theorem simple_graph_indepNum_le_one_imp_eq_top {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hα : G.indepNum ≤ 1) : G = ⊤ := by
  ext u v
  rw [SimpleGraph.top_adj]
  constructor
  · intro h
    exact G.ne_of_adj h
  · intro hne
    by_contra h_not_adj
    have h_indep : G.IsIndepSet ({u, v} : Set V) := by
      rw [SimpleGraph.IsIndepSet, Set.pairwise_pair]
      intro _
      exact ⟨h_not_adj, fun hvu => h_not_adj (G.adj_symm hvu)⟩
    have h_indep' : G.IsIndepSet ↑({u, v} : Finset V) := by
      rwa [Finset.coe_pair]
    have h_card_le := h_indep'.card_le_indepNum
    have h_card : ({u, v} : Finset V).card = 2 := Finset.card_pair_eq_two_iff.mpr hne
    rw [h_card] at h_card_le
    omega
