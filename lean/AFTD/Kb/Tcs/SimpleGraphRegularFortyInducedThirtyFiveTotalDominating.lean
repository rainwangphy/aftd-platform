import AFTD.Prelude

/-!
# simple_graph_regular_forty_induced_thirty_five_total_dominating

Topic: combinatorics   Node: 5891d0d0f13a

Provenance: helper lemma. Structural link between the induced-35 and total-domination branches for OP-926.

In a triangle-free 9-regular graph on 40 vertices, the complement of an induced 8-regular 35-vertex subgraph is a total dominating five-set.
-/

lemma simple_graph_regular_forty_induced_thirty_five_total_dominating_four_vertex
    {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) [DecidableRel H.Adj] (U : Finset α)
    (hcf : H.CliqueFree 3) (hU : U.card = 4)
    (hsum : ∑ u ∈ U, (H.neighborFinset u ∩ U).card = 10) : False := by
  classical
  have hle3 : ∀ u ∈ U, (H.neighborFinset u ∩ U).card ≤ 3 := by
    intro u hu
    have hsub : H.neighborFinset u ∩ U ⊆ U.erase u := by
      intro w hw
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
      rw [Finset.mem_erase]
      exact ⟨(H.ne_of_adj hw.1).symm, hw.2⟩
    calc (H.neighborFinset u ∩ U).card ≤ (U.erase u).card := Finset.card_le_card hsub
      _ = 3 := by rw [Finset.card_erase_of_mem hu, hU]
  have hex : ∃ u ∈ U, (H.neighborFinset u ∩ U).card = 3 := by
    by_contra hc
    push Not at hc
    have hle2 : ∀ u ∈ U, (H.neighborFinset u ∩ U).card ≤ 2 := by
      intro u hu
      have := hle3 u hu
      have := hc u hu
      omega
    have hble : ∑ u ∈ U, (H.neighborFinset u ∩ U).card ≤ ∑ u ∈ U, (2:ℕ) := Finset.sum_le_sum hle2
    have h2 : ∑ u ∈ U, (2:ℕ) = 8 := by rw [Finset.sum_const, hU]; norm_num
    rw [hsum, h2] at hble
    omega
  obtain ⟨u, hu, hdu⟩ := hex
  set A : Finset α := U.erase u with hAdef
  have hAcard : A.card = 3 := by rw [hAdef, Finset.card_erase_of_mem hu, hU]
  have hsubA : H.neighborFinset u ∩ U ⊆ A := by
    intro w hw
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
    rw [hAdef, Finset.mem_erase]
    exact ⟨(H.ne_of_adj hw.1).symm, hw.2⟩
  have hAeq : H.neighborFinset u ∩ U = A :=
    Finset.eq_of_subset_of_card_le hsubA (by rw [hAcard, hdu])
  have hAa : ∀ a ∈ A, (H.neighborFinset a ∩ U).card ≤ 1 := by
    intro a haA
    have hsub1 : H.neighborFinset a ∩ U ⊆ {u} := by
      intro w hw
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
      rw [Finset.mem_singleton]
      by_contra hwu
      have hwA : w ∈ A := by rw [hAdef, Finset.mem_erase]; exact ⟨hwu, hw.2⟩
      have haN : H.Adj u a := by
        have h' : a ∈ H.neighborFinset u ∩ U := by rw [hAeq]; exact haA
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at h'
        exact h'.1
      have hwN : H.Adj u w := by
        have h' : w ∈ H.neighborFinset u ∩ U := by rw [hAeq]; exact hwA
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at h'
        exact h'.1
      exact hcf {u, a, w} (SimpleGraph.is3Clique_triple_iff.mpr ⟨haN, hwN, hw.1⟩)
    calc (H.neighborFinset a ∩ U).card ≤ ({u} : Finset α).card := Finset.card_le_card hsub1
      _ = 1 := Finset.card_singleton u
  have hUeq : U = insert u A := by rw [hAdef, Finset.insert_erase hu]
  have hnotmem : u ∉ A := by rw [hAdef]; exact Finset.notMem_erase u U
  have hsum_dec : ∑ x ∈ U, (H.neighborFinset x ∩ U).card
      = (H.neighborFinset u ∩ U).card + ∑ x ∈ A, (H.neighborFinset x ∩ U).card := by
    rw [hUeq, Finset.sum_insert hnotmem]
  have hAle : ∑ x ∈ A, (H.neighborFinset x ∩ U).card ≤ ∑ x ∈ A, (1:ℕ) := Finset.sum_le_sum hAa
  have hA1 : ∑ x ∈ A, (1:ℕ) = 3 := by rw [Finset.sum_const, hAcard]; norm_num
  rw [hsum_dec, hdu] at hsum
  omega

theorem simple_graph_regular_forty_induced_thirty_five_total_dominating
    (G : SimpleGraph (Fin 40)) [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) (hreg : ∀ v, G.degree v = 9)
    (S : Finset (Fin 40)) (hcard : S.card = 35)
    (hinner : ∀ v ∈ S, ((G.neighborFinset v) ∩ S).card = 8) :
    ∀ x, ∃ t ∈ (Finset.univ \ S), G.Adj t x := by
  classical
  set T : Finset (Fin 40) := Finset.univ \ S with hT
  have hTmem : ∀ w : Fin 40, w ∈ T ↔ w ∉ S := by
    intro w; rw [hT]; simp
  have hTcard : T.card = 5 := by
    rw [hT, Finset.card_sdiff]; simp [hcard]
  have hTeq : ∀ v : Fin 40, G.neighborFinset v ∩ T = G.neighborFinset v \ S := by
    intro v; ext w; rw [hT]; simp
  have hS1 : ∀ v ∈ S, (G.neighborFinset v ∩ T).card = 1 := by
    intro v hv
    have h9 : (G.neighborFinset v).card = 9 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hreg v
    have h8 : (G.neighborFinset v ∩ S).card = 8 := hinner v hv
    have hsp := Finset.card_inter_add_card_sdiff (G.neighborFinset v) S
    rw [hTeq]
    omega
  have hcross : (∑ v ∈ S, (G.neighborFinset v ∩ T).card)
      = ∑ t ∈ T, (G.neighborFinset t ∩ S).card := by
    have hrow : ∀ (v : Fin 40) (W : Finset (Fin 40)),
        (G.neighborFinset v ∩ W).card = ∑ w ∈ W, (if G.Adj v w then 1 else 0) := by
      intro v W
      have : G.neighborFinset v ∩ W = W.filter (G.Adj v) := by
        ext w; simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]; tauto
      rw [this, Finset.card_filter]
    have hcol : ∀ (t : Fin 40) (W : Finset (Fin 40)),
        (G.neighborFinset t ∩ W).card = ∑ v ∈ W, (if G.Adj v t then 1 else 0) := by
      intro t W
      have : G.neighborFinset t ∩ W = W.filter (fun v => G.Adj v t) := by
        ext w; simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
        rw [SimpleGraph.adj_comm]; tauto
      rw [this, Finset.card_filter]
    rw [Finset.sum_congr rfl (fun v _ => hrow v T), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [hcol t S]
  have hsumS : (∑ v ∈ S, (G.neighborFinset v ∩ T).card) = 35 := by
    rw [Finset.sum_congr rfl (fun v hv => hS1 v hv)]
    rw [Finset.sum_const, hcard]; norm_num
  have hcross35 : (∑ t ∈ T, (G.neighborFinset t ∩ S).card) = 35 := by
    rw [← hcross]; exact hsumS
  have hsplit : ∀ t : Fin 40,
      (G.neighborFinset t ∩ S).card + (G.neighborFinset t ∩ T).card = 9 := by
    intro t
    have h9 : (G.neighborFinset t).card = 9 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hreg t
    have hsp := Finset.card_inter_add_card_sdiff (G.neighborFinset t) S
    rw [← hTeq t] at hsp
    omega
  have hsumT : (∑ t ∈ T, (G.neighborFinset t ∩ T).card) = 10 := by
    have h45 : (∑ t ∈ T, ((G.neighborFinset t ∩ S).card + (G.neighborFinset t ∩ T).card)) = 45 := by
      rw [Finset.sum_congr rfl (fun t _ => hsplit t)]
      rw [Finset.sum_const, hTcard]; norm_num
    rw [Finset.sum_add_distrib, hcross35] at h45
    omega
  intro x
  by_cases hx : x ∈ S
  · have hd1 : (G.neighborFinset x ∩ T).card = 1 := hS1 x hx
    have hne : (G.neighborFinset x ∩ T).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h; rw [h] at hd1; simp at hd1
    obtain ⟨t, ht⟩ := hne
    rw [Finset.mem_inter] at ht
    exact ⟨t, ht.2, ((SimpleGraph.mem_neighborFinset G x t).mp ht.1).symm⟩
  · have hxT : x ∈ T := by rw [hTmem]; exact hx
    by_contra hcon
    push Not at hcon
    have hdx0 : (G.neighborFinset x ∩ T).card = 0 := by
      have hempty : G.neighborFinset x ∩ T = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨w, hw⟩
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
        exact hcon w hw.2 hw.1.symm
      rw [hempty, Finset.card_empty]
    have hUcard : (T.erase x).card = 4 := by
      rw [Finset.card_erase_of_mem hxT, hTcard]
    have hsumU : (∑ u ∈ T.erase x, (G.neighborFinset u ∩ (T.erase x)).card) = 10 := by
      have hrew : ∀ u ∈ T.erase x, G.neighborFinset u ∩ (T.erase x) = G.neighborFinset u ∩ T := by
        intro u hu
        have hxu : x ∉ G.neighborFinset u := by
          rw [SimpleGraph.mem_neighborFinset]
          exact hcon u (Finset.mem_erase.mp hu).2
        ext w
        rw [Finset.mem_inter, Finset.mem_inter]
        constructor
        · rintro ⟨hwN, hwU⟩
          exact ⟨hwN, (Finset.mem_erase.mp hwU).2⟩
        · rintro ⟨hwN, hwT⟩
          refine ⟨hwN, ?_⟩
          rw [Finset.mem_erase]
          exact ⟨by rintro rfl; exact hxu hwN, hwT⟩
      rw [Finset.sum_congr rfl (fun u hu => by rw [hrew u hu])]
      have h := Finset.sum_erase_add T (fun t => (G.neighborFinset t ∩ T).card) hxT
      rw [hdx0] at h
      omega
    exact simple_graph_regular_forty_induced_thirty_five_total_dominating_four_vertex
      G (T.erase x) htri hUcard hsumU
