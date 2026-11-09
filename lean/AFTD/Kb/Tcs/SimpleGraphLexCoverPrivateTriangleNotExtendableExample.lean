import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.SimpleGraphStableTriangleNotInMaximumPackingExample
import AFTD.Kb.Tcs.G

/-!
# simple_graph_lex_cover_private_triangle_not_extendable_example

Topic: graphs   Node: 906fc4da85f3

Provenance: helper lemma. Independent exact computations 16075–16076; triangle packing and cover definitions from arXiv:2610.15539, Section 1.

There is a stable graph with triangle packing number two, a maximum packing P, and a minimum triangle cover C minimizing its edges outside P, such that an outside cover edge has a private triangle belonging to no maximum packing.
-/

open scoped Sym2

def simple_graph_lex_cover_private_triangle_not_extendable_example_G : SimpleGraph (Fin 5) :=
  simple_graph_stable_triangle_not_in_maximum_packing_example_G

instance simple_graph_lex_cover_private_triangle_not_extendable_example_decAdj :
    DecidableRel simple_graph_lex_cover_private_triangle_not_extendable_example_G.Adj := by
  dsimp [simple_graph_lex_cover_private_triangle_not_extendable_example_G,
    simple_graph_stable_triangle_not_in_maximum_packing_example_G]
  infer_instance

def simple_graph_lex_cover_private_triangle_not_extendable_example_P : Finset (Finset (Fin 5)) :=
  {{0, 1, 3}, {1, 2, 4}}

def simple_graph_lex_cover_private_triangle_not_extendable_example_C : Finset (Sym2 (Fin 5)) :=
  {s(0, 1), s(1, 2), s(3, 4)}

def simple_graph_lex_cover_private_triangle_not_extendable_example_e : Sym2 (Fin 5) :=
  s(3, 4)

def simple_graph_lex_cover_private_triangle_not_extendable_example_t : Finset (Fin 5) :=
  simple_graph_stable_triangle_not_in_maximum_packing_example_t

def simple_graph_lex_cover_private_triangle_not_extendable_example_EP : Finset (Sym2 (Fin 5)) :=
  (simple_graph_lex_cover_private_triangle_not_extendable_example_P.image finite_vertex_set_edge_encoding).biUnion id

lemma simple_graph_lex_cover_private_triangle_not_extendable_example_C_edges :
    ∀ g ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_C,
      g ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_G.edgeSet := by decide

lemma simple_graph_lex_cover_private_triangle_not_extendable_example_C_card :
    simple_graph_lex_cover_private_triangle_not_extendable_example_C.card = 3 := by decide

lemma simple_graph_lex_cover_private_triangle_not_extendable_example_C_covers_bounded :
  ∀ s ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 5)),
    simple_graph_lex_cover_private_triangle_not_extendable_example_G.IsNClique 3 s →
      ∃ g ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_C, ∀ x ∈ g, x ∈ s := by decide

lemma simple_graph_lex_cover_private_triangle_not_extendable_example_C_covers :
    ∀ s : Finset (Fin 5),
      simple_graph_lex_cover_private_triangle_not_extendable_example_G.IsNClique 3 s →
        ∃ g ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_C, ∀ x ∈ g, x ∈ s := by
  intro s hs
  have hs_in : s ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 5)) := by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ s, hs.2⟩
  exact simple_graph_lex_cover_private_triangle_not_extendable_example_C_covers_bounded s hs_in hs

lemma simple_graph_lex_cover_private_triangle_not_extendable_example_no_pair_covers :
  ∀ e1 e2 : Sym2 (Fin 5),
    e1 ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_G.edgeSet →
    e2 ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_G.edgeSet →
    ¬ (∀ s ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 5)),
        simple_graph_lex_cover_private_triangle_not_extendable_example_G.IsNClique 3 s →
          (∀ x ∈ e1, x ∈ s) ∨ (∀ x ∈ e2, x ∈ s)) := by
  decide

lemma simple_graph_lex_cover_private_triangle_not_extendable_example_subset_edge_two
    (s : Finset (Sym2 (Fin 5)))
    (hs : ∀ e ∈ s, e ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_G.edgeSet)
    (hcard : s.card ≤ 2) :
    ∃ a b : Sym2 (Fin 5),
      a ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_G.edgeSet ∧
      b ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_G.edgeSet ∧
      ∀ x ∈ s, x = a ∨ x = b := by
  have hedge : s(0, 1) ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_G.edgeSet := by decide
  interval_cases hc : s.card
  · rw [Finset.card_eq_zero] at hc
    refine ⟨s(0, 1), s(0, 1), hedge, hedge, ?_⟩
    intro x hx; subst hc; simp at hx
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    have ha : a ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_G.edgeSet :=
      hs a (Finset.mem_singleton_self a)
    refine ⟨a, a, ha, ha, ?_⟩
    intro x hx; rw [Finset.mem_singleton] at hx; left; exact hx
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp hc
    have ha : a ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_G.edgeSet :=
      hs a (Finset.mem_insert_self a {b})
    have hb : b ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_G.edgeSet :=
      hs b (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    refine ⟨a, b, ha, hb, ?_⟩
    intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx; exact hx

lemma simple_graph_lex_cover_private_triangle_not_extendable_example_no_cover_card_le_two
    (F : Finset (Sym2 (Fin 5)))
    (hF_edge : ∀ e ∈ F, e ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_G.edgeSet)
    (hF_cover : ∀ s : Finset (Fin 5),
      simple_graph_lex_cover_private_triangle_not_extendable_example_G.IsNClique 3 s →
        ∃ e ∈ F, ∀ x ∈ e, x ∈ s) :
    ¬ F.card ≤ 2 := by
  intro hle
  obtain ⟨a, b, ha, hb, hab⟩ :=
    simple_graph_lex_cover_private_triangle_not_extendable_example_subset_edge_two F hF_edge hle
  have h_contra := simple_graph_lex_cover_private_triangle_not_extendable_example_no_pair_covers a b ha hb
  apply h_contra
  intro s hs hs_clique
  obtain ⟨e, he_in, he_sub⟩ := hF_cover s hs_clique
  rcases hab e he_in with rfl | rfl
  · left; exact he_sub
  · right; exact he_sub

lemma simple_graph_lex_cover_private_triangle_not_extendable_example_G_cover_number :
    simple_graph_triangle_cover_number simple_graph_lex_cover_private_triangle_not_extendable_example_G = 3 := by
  dsimp [simple_graph_triangle_cover_number]
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨simple_graph_lex_cover_private_triangle_not_extendable_example_C,
      simple_graph_lex_cover_private_triangle_not_extendable_example_C_edges,
      simple_graph_lex_cover_private_triangle_not_extendable_example_C_covers,
      simple_graph_lex_cover_private_triangle_not_extendable_example_C_card⟩
  · rintro n ⟨F, hF_edge, hF_cover, rfl⟩
    by_contra! hlt
    have hle : F.card ≤ 2 := Nat.lt_succ_iff.mp (by omega)
    exact simple_graph_lex_cover_private_triangle_not_extendable_example_no_cover_card_le_two F hF_edge hF_cover hle

lemma simple_graph_lex_cover_private_triangle_not_extendable_example_C_diff_EP_card :
    (simple_graph_lex_cover_private_triangle_not_extendable_example_C \
      simple_graph_lex_cover_private_triangle_not_extendable_example_EP).card = 1 := by decide

lemma simple_graph_lex_cover_private_triangle_not_extendable_example_no_cover_inside_EP :
  ∀ e1 e2 e3 : Sym2 (Fin 5),
    e1 ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_EP →
    e2 ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_EP →
    e3 ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_EP →
    ¬ (∀ s ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 5)),
        simple_graph_lex_cover_private_triangle_not_extendable_example_G.IsNClique 3 s →
          (∀ x ∈ e1, x ∈ s) ∨ (∀ x ∈ e2, x ∈ s) ∨ (∀ x ∈ e3, x ∈ s)) := by
  decide

lemma simple_graph_lex_cover_private_triangle_not_extendable_example_cover_min_outside
    (D : Finset (Sym2 (Fin 5)))
    (hD_cover : ∀ s : Finset (Fin 5),
      simple_graph_lex_cover_private_triangle_not_extendable_example_G.IsNClique 3 s →
        ∃ g ∈ D, ∀ x ∈ g, x ∈ s)
    (hD_card : D.card = simple_graph_triangle_cover_number
      simple_graph_lex_cover_private_triangle_not_extendable_example_G) :
    (simple_graph_lex_cover_private_triangle_not_extendable_example_C \
      simple_graph_lex_cover_private_triangle_not_extendable_example_EP).card ≤
    (D \ simple_graph_lex_cover_private_triangle_not_extendable_example_EP).card := by
  rw [simple_graph_lex_cover_private_triangle_not_extendable_example_G_cover_number] at hD_card
  rw [simple_graph_lex_cover_private_triangle_not_extendable_example_C_diff_EP_card]
  by_contra! hlt
  have h_zero : (D \ simple_graph_lex_cover_private_triangle_not_extendable_example_EP).card = 0 := by omega
  rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at h_zero
  obtain ⟨d1, d2, d3, -, -, -, rfl⟩ := Finset.card_eq_three.mp hD_card
  have hd1 : d1 ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_EP :=
    h_zero (Finset.mem_insert_self d1 {d2, d3})
  have hd2 : d2 ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_EP :=
    h_zero (Finset.mem_insert_of_mem (Finset.mem_insert_self d2 {d3}))
  have hd3 : d3 ∈ simple_graph_lex_cover_private_triangle_not_extendable_example_EP :=
    h_zero (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self d3)))
  have h_contra :=
    simple_graph_lex_cover_private_triangle_not_extendable_example_no_cover_inside_EP d1 d2 d3 hd1 hd2 hd3
  apply h_contra
  intro s hs hs_clique
  obtain ⟨g, hg_in, hg_sub⟩ := hD_cover s hs_clique
  simp only [Finset.mem_insert, Finset.mem_singleton] at hg_in
  rcases hg_in with rfl | rfl | rfl
  · left; exact hg_sub
  · right; left; exact hg_sub
  · right; right; exact hg_sub

theorem simple_graph_lex_cover_private_triangle_not_extendable_example :
    ∃ (G : SimpleGraph (Fin 5)) (P : Finset (Finset (Fin 5)))
      (C : Finset (Sym2 (Fin 5))) (e : Sym2 (Fin 5)) (t : Finset (Fin 5)),
      simple_graph_triangle_packing_number G = 2 ∧ simple_graph_triangle_cover_number G = 3 ∧
      (∀ g ∈ G.edgeSet,
        simple_graph_triangle_packing_number (G.deleteEdges {g}) =
          simple_graph_triangle_packing_number G) ∧
      (∀ s ∈ P, G.IsNClique 3 s) ∧
      (P : Set (Finset (Fin 5))).Pairwise (fun a b => (a ∩ b).card ≤ 1) ∧
      P.card = simple_graph_triangle_packing_number G ∧
      (∀ g ∈ C, g ∈ G.edgeSet) ∧
      (∀ s : Finset (Fin 5), G.IsNClique 3 s → ∃ g ∈ C, ∀ x ∈ g, x ∈ s) ∧
      C.card = simple_graph_triangle_cover_number G ∧
      (∀ D : Finset (Sym2 (Fin 5)),
        (∀ g ∈ D, g ∈ G.edgeSet) →
        (∀ s : Finset (Fin 5), G.IsNClique 3 s → ∃ g ∈ D, ∀ x ∈ g, x ∈ s) →
        D.card = simple_graph_triangle_cover_number G →
        (C \ (P.image finite_vertex_set_edge_encoding).biUnion id).card ≤
          (D \ (P.image finite_vertex_set_edge_encoding).biUnion id).card) ∧
      e ∈ C \ (P.image finite_vertex_set_edge_encoding).biUnion id ∧
      G.IsNClique 3 t ∧ (∀ x ∈ e, x ∈ t) ∧
      (∀ g ∈ C, (∀ x ∈ g, x ∈ t) → g = e) ∧
      ∀ Q : Finset (Finset (Fin 5)),
        (∀ s ∈ Q, G.IsNClique 3 s) →
        (Q : Set (Finset (Fin 5))).Pairwise (fun a b => (a ∩ b).card ≤ 1) →
        Q.card = simple_graph_triangle_packing_number G → t ∉ Q := by
  refine ⟨simple_graph_lex_cover_private_triangle_not_extendable_example_G,
          simple_graph_lex_cover_private_triangle_not_extendable_example_P,
          simple_graph_lex_cover_private_triangle_not_extendable_example_C,
          simple_graph_lex_cover_private_triangle_not_extendable_example_e,
          simple_graph_lex_cover_private_triangle_not_extendable_example_t,
          simple_graph_stable_triangle_not_in_maximum_packing_example_G_packing_number,
          simple_graph_lex_cover_private_triangle_not_extendable_example_G_cover_number,
          simple_graph_stable_triangle_not_in_maximum_packing_example_delete_edges_packing_number,
          by decide, by decide, ?_,
          simple_graph_lex_cover_private_triangle_not_extendable_example_C_edges,
          simple_graph_lex_cover_private_triangle_not_extendable_example_C_covers,
          ?_, ?_, by decide, by decide, by decide, by decide, ?_⟩
  · dsimp [simple_graph_lex_cover_private_triangle_not_extendable_example_G]
    rw [simple_graph_stable_triangle_not_in_maximum_packing_example_G_packing_number]
    decide
  · rw [simple_graph_lex_cover_private_triangle_not_extendable_example_G_cover_number]; decide
  · intro D hD_edge hD_cover hD_card
    exact simple_graph_lex_cover_private_triangle_not_extendable_example_cover_min_outside D hD_cover hD_card
  · intro Q hQ_clique hQ_pw hQ_card ht_in
    dsimp [simple_graph_lex_cover_private_triangle_not_extendable_example_G,
           simple_graph_lex_cover_private_triangle_not_extendable_example_t] at *
    rw [simple_graph_stable_triangle_not_in_maximum_packing_example_G_packing_number] at hQ_card
    have h_erase : (Q.erase simple_graph_stable_triangle_not_in_maximum_packing_example_t).card = 1 := by
      rw [Finset.card_erase_of_mem ht_in, hQ_card]
    obtain ⟨s, hs⟩ := Finset.card_eq_one.mp h_erase
    have hs_in_erase : s ∈ Q.erase simple_graph_stable_triangle_not_in_maximum_packing_example_t :=
      hs ▸ Finset.mem_singleton_self s
    rw [Finset.mem_erase] at hs_in_erase
    have hs_ne : s ≠ simple_graph_stable_triangle_not_in_maximum_packing_example_t := hs_in_erase.1
    have hs_in : s ∈ Q := hs_in_erase.2
    have hs_nclique := hQ_clique s hs_in
    have hs_mem_powerset : s ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 5)) := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ s, hs_nclique.2⟩
    have hs_pw : (simple_graph_stable_triangle_not_in_maximum_packing_example_t ∩ s).card ≤ 1 :=
      hQ_pw ht_in hs_in (Ne.symm hs_ne)
    have hs_not_clique :=
      simple_graph_stable_triangle_not_in_maximum_packing_example_t_no_compatible s hs_mem_powerset hs_pw
    exact hs_not_clique hs_nclique.1
