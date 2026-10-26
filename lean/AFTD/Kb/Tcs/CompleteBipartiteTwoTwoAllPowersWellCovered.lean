import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower

/-!
# complete_bipartite_two_two_all_powers_well_covered

Topic: graphs   Node: 11aaf943d04c

Provenance: formalization of a published result. Source: Deniz 2022; arXiv:2610.09300 Theorem 1.3

For every positive integer d, the d-th power of the complete bipartite graph K_{2,2} is well-covered.
-/

open SimpleGraph

private def complete_bipartite_two_two_all_powers_well_covered_K22 :=
  completeBipartiteGraph (Fin 2) (Fin 2)

private def complete_bipartite_two_two_all_powers_well_covered_leftSet :
    Finset (Fin 2 ⊕ Fin 2) := Finset.univ.image Sum.inl

private def complete_bipartite_two_two_all_powers_well_covered_rightSet :
    Finset (Fin 2 ⊕ Fin 2) := Finset.univ.image Sum.inr

private lemma complete_bipartite_two_two_all_powers_well_covered_leftSet_card :
    complete_bipartite_two_two_all_powers_well_covered_leftSet.card = 2 := by
  rw [complete_bipartite_two_two_all_powers_well_covered_leftSet,
      Finset.card_image_of_injective _ Sum.inl_injective]
  simp

private lemma complete_bipartite_two_two_all_powers_well_covered_rightSet_card :
    complete_bipartite_two_two_all_powers_well_covered_rightSet.card = 2 := by
  rw [complete_bipartite_two_two_all_powers_well_covered_rightSet,
      Finset.card_image_of_injective _ Sum.inr_injective]
  simp

private lemma complete_bipartite_two_two_all_powers_well_covered_leftSet_indep :
    complete_bipartite_two_two_all_powers_well_covered_K22.IsIndepSet
      (complete_bipartite_two_two_all_powers_well_covered_leftSet : Set (Fin 2 ⊕ Fin 2)) := by
  intro u hu v hv hne
  simp only [complete_bipartite_two_two_all_powers_well_covered_leftSet,
             Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hu hv
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  simp [complete_bipartite_two_two_all_powers_well_covered_K22, completeBipartiteGraph]

private lemma complete_bipartite_two_two_all_powers_well_covered_rightSet_indep :
    complete_bipartite_two_two_all_powers_well_covered_K22.IsIndepSet
      (complete_bipartite_two_two_all_powers_well_covered_rightSet : Set (Fin 2 ⊕ Fin 2)) := by
  intro u hu v hv hne
  simp only [complete_bipartite_two_two_all_powers_well_covered_rightSet,
             Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hu hv
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  simp [complete_bipartite_two_two_all_powers_well_covered_K22, completeBipartiteGraph]

private lemma complete_bipartite_two_two_all_powers_well_covered_indep_subset
    (s : Finset (Fin 2 ⊕ Fin 2))
    (hs : complete_bipartite_two_two_all_powers_well_covered_K22.IsIndepSet
      (s : Set (Fin 2 ⊕ Fin 2))) :
    s ⊆ complete_bipartite_two_two_all_powers_well_covered_leftSet ∨
    s ⊆ complete_bipartite_two_two_all_powers_well_covered_rightSet := by
  by_cases hleft : ∃ a : Fin 2, Sum.inl a ∈ s
  · left
    obtain ⟨a, ha⟩ := hleft
    intro x hx
    rcases x with b | b
    · simp [complete_bipartite_two_two_all_powers_well_covered_leftSet]
    · exfalso
      have hadj : complete_bipartite_two_two_all_powers_well_covered_K22.Adj
          (Sum.inl a) (Sum.inr b) := by
        simp [complete_bipartite_two_two_all_powers_well_covered_K22, completeBipartiteGraph]
      have hne : (Sum.inl a : Fin 2 ⊕ Fin 2) ≠ Sum.inr b := by simp
      exact hs (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hx) hne hadj
  · right
    intro x hx
    rcases x with b | b
    · exfalso
      exact hleft ⟨b, hx⟩
    · simp [complete_bipartite_two_two_all_powers_well_covered_rightSet]

private lemma complete_bipartite_two_two_all_powers_well_covered_K22_maximal_indep_card
    (s : Finset (Fin 2 ⊕ Fin 2))
    (hs : Maximal (fun (u : Finset (Fin 2 ⊕ Fin 2)) =>
      complete_bipartite_two_two_all_powers_well_covered_K22.IsIndepSet
        (u : Set (Fin 2 ⊕ Fin 2))) s) :
    s.card = 2 := by
  rcases complete_bipartite_two_two_all_powers_well_covered_indep_subset s hs.1 with h | h
  · have h_eq : s = complete_bipartite_two_two_all_powers_well_covered_leftSet :=
      le_antisymm h (hs.2 complete_bipartite_two_two_all_powers_well_covered_leftSet_indep h)
    rw [h_eq, complete_bipartite_two_two_all_powers_well_covered_leftSet_card]
  · have h_eq : s = complete_bipartite_two_two_all_powers_well_covered_rightSet :=
      le_antisymm h (hs.2 complete_bipartite_two_two_all_powers_well_covered_rightSet_indep h)
    rw [h_eq, complete_bipartite_two_two_all_powers_well_covered_rightSet_card]

private lemma complete_bipartite_two_two_all_powers_well_covered_K22_well_covered :
    simple_graph_is_well_covered complete_bipartite_two_two_all_powers_well_covered_K22 := by
  intro s t hs ht
  rw [complete_bipartite_two_two_all_powers_well_covered_K22_maximal_indep_card s hs,
      complete_bipartite_two_two_all_powers_well_covered_K22_maximal_indep_card t ht]

private lemma complete_bipartite_two_two_all_powers_well_covered_power_one_eq_self
    {V : Type*} (G : SimpleGraph V) :
    simple_graph_power G 1 = G := by
  ext u v
  show u ≠ v ∧ G.edist u v ≤ (1 : ℕ) ↔ G.Adj u v
  norm_cast
  rw [edist_le_one_iff_adj_or_eq]
  constructor
  · rintro ⟨hne, h | rfl⟩
    · exact h
    · exact (hne rfl).elim
  · intro h
    exact ⟨h.ne, Or.inl h⟩

private lemma complete_bipartite_two_two_all_powers_well_covered_edist_le_two
    (u v : Fin 2 ⊕ Fin 2) :
    complete_bipartite_two_two_all_powers_well_covered_K22.edist u v ≤ 2 := by
  rcases u with a | a <;> rcases v with b | b
  · have h1 : complete_bipartite_two_two_all_powers_well_covered_K22.Adj (Sum.inl a) (Sum.inr 0) := by
      simp [complete_bipartite_two_two_all_powers_well_covered_K22, completeBipartiteGraph]
    have h2 : complete_bipartite_two_two_all_powers_well_covered_K22.Adj (Sum.inr 0) (Sum.inl b) := by
      simp [complete_bipartite_two_two_all_powers_well_covered_K22, completeBipartiteGraph]
    have h1_dist : complete_bipartite_two_two_all_powers_well_covered_K22.edist (Sum.inl a) (Sum.inr 0) = 1 :=
      edist_eq_one_iff_adj.mpr h1
    have h2_dist : complete_bipartite_two_two_all_powers_well_covered_K22.edist (Sum.inr 0) (Sum.inl b) = 1 :=
      edist_eq_one_iff_adj.mpr h2
    have h_tri : complete_bipartite_two_two_all_powers_well_covered_K22.edist (Sum.inl a) (Sum.inl b) ≤
        complete_bipartite_two_two_all_powers_well_covered_K22.edist (Sum.inl a) (Sum.inr 0) +
        complete_bipartite_two_two_all_powers_well_covered_K22.edist (Sum.inr 0) (Sum.inl b) :=
      SimpleGraph.edist_triangle
    rw [h1_dist, h2_dist] at h_tri
    exact h_tri
  · have h : complete_bipartite_two_two_all_powers_well_covered_K22.Adj (Sum.inl a) (Sum.inr b) := by
      simp [complete_bipartite_two_two_all_powers_well_covered_K22, completeBipartiteGraph]
    rw [edist_eq_one_iff_adj.mpr h]
    decide
  · have h : complete_bipartite_two_two_all_powers_well_covered_K22.Adj (Sum.inr a) (Sum.inl b) := by
      simp [complete_bipartite_two_two_all_powers_well_covered_K22, completeBipartiteGraph]
    rw [edist_eq_one_iff_adj.mpr h]
    decide
  · have h1 : complete_bipartite_two_two_all_powers_well_covered_K22.Adj (Sum.inr a) (Sum.inl 0) := by
      simp [complete_bipartite_two_two_all_powers_well_covered_K22, completeBipartiteGraph]
    have h2 : complete_bipartite_two_two_all_powers_well_covered_K22.Adj (Sum.inl 0) (Sum.inr b) := by
      simp [complete_bipartite_two_two_all_powers_well_covered_K22, completeBipartiteGraph]
    have h1_dist : complete_bipartite_two_two_all_powers_well_covered_K22.edist (Sum.inr a) (Sum.inl 0) = 1 :=
      edist_eq_one_iff_adj.mpr h1
    have h2_dist : complete_bipartite_two_two_all_powers_well_covered_K22.edist (Sum.inl 0) (Sum.inr b) = 1 :=
      edist_eq_one_iff_adj.mpr h2
    have h_tri : complete_bipartite_two_two_all_powers_well_covered_K22.edist (Sum.inr a) (Sum.inr b) ≤
        complete_bipartite_two_two_all_powers_well_covered_K22.edist (Sum.inr a) (Sum.inl 0) +
        complete_bipartite_two_two_all_powers_well_covered_K22.edist (Sum.inl 0) (Sum.inr b) :=
      SimpleGraph.edist_triangle
    rw [h1_dist, h2_dist] at h_tri
    exact h_tri

private lemma complete_bipartite_two_two_all_powers_well_covered_power_ge_two_eq_top
    (d : ℕ) (hd : 2 ≤ d) :
    simple_graph_power complete_bipartite_two_two_all_powers_well_covered_K22 d = ⊤ := by
  ext u v
  simp only [simple_graph_power, top_adj]
  refine ⟨fun h => h.1, fun h => ⟨h,
    (complete_bipartite_two_two_all_powers_well_covered_edist_le_two u v).trans ?_⟩⟩
  exact_mod_cast hd

private lemma complete_bipartite_two_two_all_powers_well_covered_top_indep_card_le_one
    {V : Type*} (s : Finset V)
    (hs : (⊤ : SimpleGraph V).IsIndepSet (s : Set V)) : s.card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro u v hu hv
  by_contra hne
  exact hs hu hv hne hne

private lemma complete_bipartite_two_two_all_powers_well_covered_singleton_is_indep
    {V : Type*} (G : SimpleGraph V) (v : V) :
    G.IsIndepSet ({v} : Set V) := by
  intro a ha b hb hab
  simp only [Set.mem_singleton_iff] at ha hb
  rw [ha, hb] at hab
  exact False.elim (hab rfl)

private lemma complete_bipartite_two_two_all_powers_well_covered_well_covered_top
    {V : Type*} [Fintype V] [Nonempty V] :
    simple_graph_is_well_covered (⊤ : SimpleGraph V) := by
  intro s t hs ht
  have h_card (u : Finset V)
      (hu : Maximal (fun (x : Finset V) => (⊤ : SimpleGraph V).IsIndepSet (x : Set V)) u) :
      u.card = 1 := by
    have hle := complete_bipartite_two_two_all_powers_well_covered_top_indep_card_le_one u hu.1
    have hne : u.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      subst he
      obtain ⟨x⟩ := ‹Nonempty V›
      have hsing : (⊤ : SimpleGraph V).IsIndepSet (({x} : Finset V) : Set V) := by
        simp only [Finset.coe_singleton]
        exact complete_bipartite_two_two_all_powers_well_covered_singleton_is_indep ⊤ x
      have hle_empty : (∅ : Finset V) ≤ {x} := Finset.empty_subset _
      have hmax := hu.2 hsing hle_empty
      have : x ∈ (∅ : Finset V) := hmax (Finset.mem_singleton_self x)
      exact Finset.notMem_empty x this
    exact le_antisymm hle (Finset.card_pos.mpr hne)
  rw [h_card s hs, h_card t ht]

/-- Every power of the complete bipartite graph K_{2,2} is well-covered. -/
theorem complete_bipartite_two_two_all_powers_well_covered :
    ∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power (completeBipartiteGraph (Fin 2) (Fin 2)) d) := by
  intro d hd
  obtain rfl | hd2 : d = 1 ∨ 2 ≤ d := by omega
  · rw [complete_bipartite_two_two_all_powers_well_covered_power_one_eq_self]
    exact complete_bipartite_two_two_all_powers_well_covered_K22_well_covered
  · change simple_graph_is_well_covered (simple_graph_power complete_bipartite_two_two_all_powers_well_covered_K22 d)
    rw [complete_bipartite_two_two_all_powers_well_covered_power_ge_two_eq_top _ hd2]
    exact complete_bipartite_two_two_all_powers_well_covered_well_covered_top
