import AFTD.Prelude

/-!
# simple_graph_sum_choose_degree_two_le_choose_card_edgeFinset

Topic: graphs   Node: 57b4e447aabf

Provenance: helper lemma. Helper for arXiv:2610.12109 (Sharp linear Turán remainders for cycle and edge extremality), Lemma 2.5 (upper bound σ₂(T) ≤ C(k−1,2)); holds for every simple graph.

In any finite simple graph, the number of pairs of edges sharing a vertex, ∑_v C(d(v),2), is at most C(|E|,2): two distinct edges share at most one vertex.
-/

theorem simple_graph_sum_choose_degree_two_le_choose_card_edgeFinset {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, (G.degree v).choose 2 ≤ G.edgeFinset.card.choose 2 := by
  classical
  have hdeg : ∀ v, (G.degree v).choose 2 = ((G.incidenceFinset v).powersetCard 2).card := by
    intro v
    rw [Finset.card_powersetCard, SimpleGraph.card_incidenceFinset_eq_degree]
  simp_rw [hdeg]
  rw [← Finset.card_sigma, ← Finset.card_powersetCard]
  apply Finset.card_le_card_of_injOn (fun p => p.2)
  · intro p hp
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_univ, true_and,
      Finset.mem_powersetCard] at hp ⊢
    exact ⟨hp.1.trans (fun e he => by
      have := (SimpleGraph.incidenceFinset_subset G p.1) he
      exact this), hp.2⟩
  · intro p hp q hq hpq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_univ, true_and,
      Finset.mem_powersetCard] at hp hq
    simp only at hpq
    obtain ⟨v, s⟩ := p
    obtain ⟨w, t⟩ := q
    simp only at hpq hp hq
    subst hpq
    by_cases hvw : v = w
    · subst hvw; rfl
    · exfalso
      obtain ⟨e₁, e₂, hne, rfl⟩ := Finset.card_eq_two.1 hp.2
      have h1v := hp.1 (Finset.mem_insert_self _ _)
      have h2v := hp.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have h1w := hq.1 (Finset.mem_insert_self _ _)
      have h2w := hq.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rw [SimpleGraph.mem_incidenceFinset] at h1v h2v h1w h2w
      apply hne
      have key : ∀ e ∈ G.incidenceSet v, e ∈ G.incidenceSet w → e = s(v, w) := by
        intro e hev hew
        obtain ⟨he, hve⟩ := hev
        obtain ⟨_, hwe⟩ := hew
        exact (Sym2.mem_and_mem_iff hvw).1 ⟨hve, hwe⟩
      rw [key _ h1v h1w, key _ h2v h2w]
