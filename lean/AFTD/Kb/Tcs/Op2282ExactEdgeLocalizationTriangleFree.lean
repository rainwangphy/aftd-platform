import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeMaxCliqueOrder
import AFTD.Kb.Tcs.EdgeMaxCliqueOrderGeTwo

/-!
# op_2282_exact_edge_localization_triangle_free

Topic: graphs   Node: 7f8e8f48ceb7

Provenance: formalization of a published result. Source: arXiv:2611.30029 after Theorem 1.4

Let G be a finite simple graph on vertex type V with at least two vertices and nonempty edgeFinset which is triangle-free (G.CliqueFree 3). In ℝ, the sum over all edges e ∈ G.edgeFinset of 1 / (SimpleGraph.turanGraph (Fintype.card V) (edge_max_clique_order G e)).edgeFinset.card is at most 1, with equality if and only if G is isomorphic to the Turán graph SimpleGraph.turanGraph (Fintype.card V) 2.
-/

/-- The exact edge localization of Turan's theorem holds for all triangle-free graphs (Mantel's theorem case). -/
theorem op_2282_exact_edge_localization_triangle_free
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (hne : G.edgeFinset.Nonempty)
    (htf : G.CliqueFree 3) :
    (∑ e ∈ G.edgeFinset, (1 : ℝ) / (SimpleGraph.turanGraph (Fintype.card V) (edge_max_clique_order G e)).edgeFinset.card ≤ 1) ∧
    ((∑ e ∈ G.edgeFinset, (1 : ℝ) / (SimpleGraph.turanGraph (Fintype.card V) (edge_max_clique_order G e)).edgeFinset.card = 1) ↔
      Nonempty (G ≃g SimpleGraph.turanGraph (Fintype.card V) 2)) := by
  have _ := hn
  have h_clique_order : ∀ e ∈ G.edgeFinset, edge_max_clique_order G e = 2 := by
    intro e he
    have h2 : 2 ≤ edge_max_clique_order G e := edge_max_clique_order_ge_two G he
    have hle : edge_max_clique_order G e ≤ 2 := by
      unfold edge_max_clique_order
      refine Finset.sup_le ?_
      intro s hs
      simp only [Finset.mem_filter] at hs
      have hc := hs.2.1
      by_contra! h
      obtain ⟨t, hts, ht3⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ s.card)
      have htc : G.IsClique (t : Set V) := hc.subset (Finset.coe_subset.mpr hts)
      exact htf t ⟨htc, ht3⟩
    omega
  have h_sum_eq : (∑ e ∈ G.edgeFinset, (1 : ℝ) / (SimpleGraph.turanGraph (Fintype.card V) (edge_max_clique_order G e)).edgeFinset.card) =
      (G.edgeFinset.card : ℝ) / (SimpleGraph.turanGraph (Fintype.card V) 2).edgeFinset.card := by
    have h_terms : ∀ e ∈ G.edgeFinset,
        (1 : ℝ) / (SimpleGraph.turanGraph (Fintype.card V) (edge_max_clique_order G e)).edgeFinset.card =
        (1 : ℝ) / (SimpleGraph.turanGraph (Fintype.card V) 2).edgeFinset.card := by
      intro e he
      rw [h_clique_order e he]
    rw [Finset.sum_congr rfl h_terms, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [h_sum_eq]
  have h_top_free : (⊤ : SimpleGraph (Fin 3)).Free G := by
    have hc : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
    rw [← hc] at htf
    exact SimpleGraph.cliqueFree_iff_top_free.mp htf
  have h_ext : SimpleGraph.extremalNumber (Fintype.card V) (⊤ : SimpleGraph (Fin 3)) =
      (SimpleGraph.turanGraph (Fintype.card V) 2).edgeFinset.card := by
    have := @SimpleGraph.extremalNumber_top (Fintype.card V) (Fin 3) _ _
    have hc : Fintype.card (Fin 3) - 1 = 2 := by decide
    rw [hc] at this
    exact this
  have h_le_card : G.edgeFinset.card ≤ (SimpleGraph.turanGraph (Fintype.card V) 2).edgeFinset.card := by
    rw [← h_ext]
    exact SimpleGraph.card_edgeFinset_le_extremalNumber h_top_free
  have h_pos_T : 0 < (SimpleGraph.turanGraph (Fintype.card V) 2).edgeFinset.card := by
    have h_pos_G : 0 < G.edgeFinset.card := Finset.Nonempty.card_pos hne
    exact lt_of_lt_of_le h_pos_G h_le_card
  have h_pos_T_real : (0 : ℝ) < (SimpleGraph.turanGraph (Fintype.card V) 2).edgeFinset.card :=
    Nat.cast_pos.mpr h_pos_T
  have h_card_iso : G.edgeFinset.card = (SimpleGraph.turanGraph (Fintype.card V) 2).edgeFinset.card ↔
      Nonempty (G ≃g SimpleGraph.turanGraph (Fintype.card V) 2) := by
    have h_iso_thm := @SimpleGraph.card_edgeFinset_eq_extremalNumber_top_iff_nonempty_iso_turanGraph V _ G _ (Fin 3) _ _
    have hc : Fintype.card (Fin 3) - 1 = 2 := by decide
    rw [hc, h_ext] at h_iso_thm
    exact ⟨fun heq => h_iso_thm.mp ⟨h_top_free, heq⟩, fun h => (h_iso_thm.mpr h).2⟩
  constructor
  · rw [div_le_one h_pos_T_real]
    exact Nat.cast_le.mpr h_le_card
  · rw [div_eq_one_iff_eq h_pos_T_real.ne']
    exact (Nat.cast_inj (R := ℝ)).trans h_card_iso
