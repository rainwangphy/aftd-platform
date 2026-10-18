import AFTD.Prelude

/-!
# crossing_pairs_card_eq_crossing_edges_card

Topic: graphs   Node: b76e44bae9e6

Provenance: helper lemma. step towards edge_connectivity_ge_min_degree_mul_lly_lower_bound_two

For a finite simple graph G and a vertex set A, the number of ordered adjacent pairs (a, b) with a ∈ A and b ∈ Aᶜ equals the number of edges of G crossing the cut (A, Aᶜ).
-/

/-- Ordered crossing pairs biject with crossing edges, so the two ways of counting a cut agree. -/
theorem crossing_pairs_card_eq_crossing_edges_card {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    ((A ×ˢ Aᶜ).filter (fun p : V × V => G.Adj p.1 p.2)).card =
      (G.edgeFinset.filter (fun e => ∃ u ∈ A, ∃ v ∈ (Aᶜ : Finset V), e = s(u, v))).card := by
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    rcases hp with ⟨hp_prod, hp_adj⟩
    rw [Finset.mem_product] at hp_prod
    refine ⟨?_, p.1, hp_prod.1, p.2, hp_prod.2, rfl⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hp_adj
  · intro p₁ hp₁ p₂ hp₂ h
    rw [Finset.mem_filter] at hp₁ hp₂
    rw [Finset.mem_product] at hp₁ hp₂
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have h_in_A : p₁.1 ∈ A := hp₁.1.1
      have h_in_compl : p₂.2 ∈ Aᶜ := hp₂.1.2
      rw [Finset.mem_compl] at h_in_compl
      rw [h1] at h_in_A
      exact h_in_compl h_in_A
  · intro e he
    rw [Finset.mem_filter] at he
    rcases he with ⟨he_edge, u, hu, v, hv, heq⟩
    refine ⟨(u, v), ?_, heq.symm⟩
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hu, hv⟩, ?_⟩
    rw [SimpleGraph.mem_edgeFinset] at he_edge
    rw [heq] at he_edge
    rw [SimpleGraph.mem_edgeSet] at he_edge
    exact he_edge
