import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_stable_triangle_not_in_maximum_packing_example

Topic: graphs   Node: 9549011c490b

Provenance: helper lemma. Explicit five-vertex computation, experiment 15967; triangle packing definition from arXiv:2610.15539, Section 1.

There is a finite graph with triangle packing number two in which every edge deletion preserves the packing number, but some triangle belongs to no maximum triangle packing.
-/

open Finset

def simple_graph_stable_triangle_not_in_maximum_packing_example_G : SimpleGraph (Fin 5) where
  Adj u v := u ≠ v ∧ ¬((u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0))

instance : DecidableRel simple_graph_stable_triangle_not_in_maximum_packing_example_G.Adj := by
  intro u v; dsimp [simple_graph_stable_triangle_not_in_maximum_packing_example_G]; infer_instance

def simple_graph_stable_triangle_not_in_maximum_packing_example_P0 : Finset (Finset (Fin 5)) :=
  { {0, 1, 3}, {1, 2, 4} }
def simple_graph_stable_triangle_not_in_maximum_packing_example_P3 : Finset (Finset (Fin 5)) :=
  { {0, 1, 4}, {2, 3, 4} }
def simple_graph_stable_triangle_not_in_maximum_packing_example_P4 : Finset (Finset (Fin 5)) :=
  { {0, 3, 4}, {1, 2, 3} }

lemma simple_graph_stable_triangle_not_in_maximum_packing_example_P0_pw :
    (simple_graph_stable_triangle_not_in_maximum_packing_example_P0 : Set (Finset (Fin 5))).Pairwise
      (fun a b => (a ∩ b).card ≤ 1) := by decide

lemma simple_graph_stable_triangle_not_in_maximum_packing_example_P3_pw :
    (simple_graph_stable_triangle_not_in_maximum_packing_example_P3 : Set (Finset (Fin 5))).Pairwise
      (fun a b => (a ∩ b).card ≤ 1) := by decide

lemma simple_graph_stable_triangle_not_in_maximum_packing_example_P4_pw :
    (simple_graph_stable_triangle_not_in_maximum_packing_example_P4 : Set (Finset (Fin 5))).Pairwise
      (fun a b => (a ∩ b).card ≤ 1) := by decide

lemma simple_graph_stable_triangle_not_in_maximum_packing_example_P0_card :
    simple_graph_stable_triangle_not_in_maximum_packing_example_P0.card = 2 := by decide

lemma simple_graph_stable_triangle_not_in_maximum_packing_example_P3_card :
    simple_graph_stable_triangle_not_in_maximum_packing_example_P3.card = 2 := by decide

lemma simple_graph_stable_triangle_not_in_maximum_packing_example_P4_card :
    simple_graph_stable_triangle_not_in_maximum_packing_example_P4.card = 2 := by decide

lemma simple_graph_stable_triangle_not_in_maximum_packing_example_P0_clique :
    ∀ t ∈ simple_graph_stable_triangle_not_in_maximum_packing_example_P0,
      simple_graph_stable_triangle_not_in_maximum_packing_example_G.IsNClique 3 t := by decide

theorem simple_graph_stable_triangle_not_in_maximum_packing_example_fin5_packing_card_le_two
    {V : Type*} [Fintype V] [DecidableEq V] (hV : Fintype.card V ≤ 5)
    (T : Finset (Finset V)) (h3 : ∀ t ∈ T, t.card = 3)
    (hpw : (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1)) :
    T.card ≤ 2 := by
  by_contra! h
  have h1 : 0 < T.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp h1
  have h2 : 0 < (T.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp h2
  have hbe : b ∈ T.erase a := hb
  rw [Finset.mem_erase] at hb
  have h3' : 0 < ((T.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem hbe, Finset.card_erase_of_mem ha]
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp h3'
  rw [Finset.mem_erase, Finset.mem_erase] at hc
  have hab_ne : a ≠ b := hb.1.symm
  have hac_ne : a ≠ c := hc.2.1.symm
  have hbc_ne : b ≠ c := hc.1.symm
  have ha_in : a ∈ T := ha
  have hb_in : b ∈ T := hb.2
  have hc_in : c ∈ T := hc.2.2
  have ha3 : a.card = 3 := h3 a ha_in
  have hb3 : b.card = 3 := h3 b hb_in
  have hc3 : c.card = 3 := h3 c hc_in
  have hab_pw : (a ∩ b).card ≤ 1 := hpw ha_in hb_in hab_ne
  have hac_pw : (a ∩ c).card ≤ 1 := hpw ha_in hc_in hac_ne
  have hbc_pw : (b ∩ c).card ≤ 1 := hpw hb_in hc_in hbc_ne
  have hub : (a ∪ b).card = a.card + b.card - (a ∩ b).card := card_union_add_card_inter a b ▸ by omega
  have hub_univ_le : (a ∪ b).card ≤ Fintype.card V := Finset.card_le_univ (a ∪ b)
  have hub_univ : a ∪ b = Finset.univ := by
    apply Finset.eq_univ_of_card
    omega
  have hc_sub : c ⊆ a ∪ b := by
    rw [hub_univ]
    exact Finset.subset_univ c
  have hc_eq : c = (c ∩ a) ∪ (c ∩ b) := by
    rw [← inter_union_distrib_left]
    exact (Finset.inter_eq_left.mpr hc_sub).symm
  have hc_card_le : c.card ≤ (c ∩ a).card + (c ∩ b).card := by
    conv_lhs => rw [hc_eq]
    exact Finset.card_union_le (c ∩ a) (c ∩ b)
  rw [Finset.inter_comm c a, Finset.inter_comm c b] at hc_card_le
  omega

theorem simple_graph_stable_triangle_not_in_maximum_packing_example_packing_number_eq_two
    (H : SimpleGraph (Fin 5))
    (T₀ : Finset (Finset (Fin 5)))
    (hT₀_clique : ∀ t ∈ T₀, H.IsNClique 3 t)
    (hT₀_pw : (T₀ : Set (Finset (Fin 5))).Pairwise (fun s t => (s ∩ t).card ≤ 1))
    (hT₀_card : T₀.card = 2) :
    simple_graph_triangle_packing_number H = 2 := by
  unfold simple_graph_triangle_packing_number
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨T₀, hT₀_clique, hT₀_pw, hT₀_card⟩
  · rintro n ⟨T, hT_clique, hT_pw, rfl⟩
    apply simple_graph_stable_triangle_not_in_maximum_packing_example_fin5_packing_card_le_two
      (by simp) T (fun t ht => (hT_clique t ht).2) hT_pw

lemma simple_graph_stable_triangle_not_in_maximum_packing_example_G_packing_number :
    simple_graph_triangle_packing_number simple_graph_stable_triangle_not_in_maximum_packing_example_G = 2 :=
  simple_graph_stable_triangle_not_in_maximum_packing_example_packing_number_eq_two
    simple_graph_stable_triangle_not_in_maximum_packing_example_G
    simple_graph_stable_triangle_not_in_maximum_packing_example_P0
    simple_graph_stable_triangle_not_in_maximum_packing_example_P0_clique
    simple_graph_stable_triangle_not_in_maximum_packing_example_P0_pw
    simple_graph_stable_triangle_not_in_maximum_packing_example_P0_card

lemma simple_graph_stable_triangle_not_in_maximum_packing_example_check_all_edges :
    ∀ e ∈ simple_graph_stable_triangle_not_in_maximum_packing_example_G.edgeFinset,
      (∀ t ∈ simple_graph_stable_triangle_not_in_maximum_packing_example_P0,
        (simple_graph_stable_triangle_not_in_maximum_packing_example_G.deleteEdges {e}).IsNClique 3 t) ∨
      (∀ t ∈ simple_graph_stable_triangle_not_in_maximum_packing_example_P3,
        (simple_graph_stable_triangle_not_in_maximum_packing_example_G.deleteEdges {e}).IsNClique 3 t) ∨
      (∀ t ∈ simple_graph_stable_triangle_not_in_maximum_packing_example_P4,
        (simple_graph_stable_triangle_not_in_maximum_packing_example_G.deleteEdges {e}).IsNClique 3 t) := by
  decide

lemma simple_graph_stable_triangle_not_in_maximum_packing_example_delete_edges_packing_number
    (e : Sym2 (Fin 5)) (he : e ∈ simple_graph_stable_triangle_not_in_maximum_packing_example_G.edgeSet) :
    simple_graph_triangle_packing_number
      (simple_graph_stable_triangle_not_in_maximum_packing_example_G.deleteEdges {e}) =
      simple_graph_triangle_packing_number simple_graph_stable_triangle_not_in_maximum_packing_example_G := by
  have he_fin : e ∈ simple_graph_stable_triangle_not_in_maximum_packing_example_G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    exact he
  have h_cases := simple_graph_stable_triangle_not_in_maximum_packing_example_check_all_edges e he_fin
  rw [simple_graph_stable_triangle_not_in_maximum_packing_example_G_packing_number]
  rcases h_cases with h0 | h3 | h4
  · exact simple_graph_stable_triangle_not_in_maximum_packing_example_packing_number_eq_two _ _ h0
      simple_graph_stable_triangle_not_in_maximum_packing_example_P0_pw
      simple_graph_stable_triangle_not_in_maximum_packing_example_P0_card
  · exact simple_graph_stable_triangle_not_in_maximum_packing_example_packing_number_eq_two _ _ h3
      simple_graph_stable_triangle_not_in_maximum_packing_example_P3_pw
      simple_graph_stable_triangle_not_in_maximum_packing_example_P3_card
  · exact simple_graph_stable_triangle_not_in_maximum_packing_example_packing_number_eq_two _ _ h4
      simple_graph_stable_triangle_not_in_maximum_packing_example_P4_pw
      simple_graph_stable_triangle_not_in_maximum_packing_example_P4_card

def simple_graph_stable_triangle_not_in_maximum_packing_example_t : Finset (Fin 5) := {1, 3, 4}

lemma simple_graph_stable_triangle_not_in_maximum_packing_example_t_clique :
    simple_graph_stable_triangle_not_in_maximum_packing_example_G.IsNClique 3
      simple_graph_stable_triangle_not_in_maximum_packing_example_t := by
  decide

lemma simple_graph_stable_triangle_not_in_maximum_packing_example_t_no_compatible :
    ∀ s ∈ powersetCard 3 (univ : Finset (Fin 5)),
      (simple_graph_stable_triangle_not_in_maximum_packing_example_t ∩ s).card ≤ 1 →
      ¬ simple_graph_stable_triangle_not_in_maximum_packing_example_G.IsClique (s : Set (Fin 5)) := by
  decide

theorem simple_graph_stable_triangle_not_in_maximum_packing_example :
    ∃ G : SimpleGraph (Fin 5),
      simple_graph_triangle_packing_number G = 2 ∧
      (∀ e ∈ G.edgeSet,
        simple_graph_triangle_packing_number (G.deleteEdges {e}) =
          simple_graph_triangle_packing_number G) ∧
      ∃ t : Finset (Fin 5), G.IsNClique 3 t ∧
        ∀ P : Finset (Finset (Fin 5)),
          (∀ s ∈ P, G.IsNClique 3 s) →
          (P : Set (Finset (Fin 5))).Pairwise (fun a b => (a ∩ b).card ≤ 1) →
          P.card = simple_graph_triangle_packing_number G → t ∉ P := by
  refine ⟨simple_graph_stable_triangle_not_in_maximum_packing_example_G,
    simple_graph_stable_triangle_not_in_maximum_packing_example_G_packing_number,
    simple_graph_stable_triangle_not_in_maximum_packing_example_delete_edges_packing_number,
    simple_graph_stable_triangle_not_in_maximum_packing_example_t,
    simple_graph_stable_triangle_not_in_maximum_packing_example_t_clique, ?_⟩
  intro P hP_clique hP_pw hP_card ht_in
  rw [simple_graph_stable_triangle_not_in_maximum_packing_example_G_packing_number] at hP_card
  have h_erase : (P.erase simple_graph_stable_triangle_not_in_maximum_packing_example_t).card = 1 := by
    rw [Finset.card_erase_of_mem ht_in, hP_card]
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp h_erase
  have hs_in_erase : s ∈ P.erase simple_graph_stable_triangle_not_in_maximum_packing_example_t :=
    hs ▸ Finset.mem_singleton_self s
  rw [Finset.mem_erase] at hs_in_erase
  have hs_ne : s ≠ simple_graph_stable_triangle_not_in_maximum_packing_example_t := hs_in_erase.1
  have hs_in : s ∈ P := hs_in_erase.2
  have hs_nclique := hP_clique s hs_in
  have hs_mem_powerset : s ∈ powersetCard 3 (univ : Finset (Fin 5)) := by
    rw [mem_powersetCard]
    exact ⟨subset_univ s, hs_nclique.2⟩
  have hs_pw : (simple_graph_stable_triangle_not_in_maximum_packing_example_t ∩ s).card ≤ 1 :=
    hP_pw ht_in hs_in (Ne.symm hs_ne)
  have hs_not_clique :=
    simple_graph_stable_triangle_not_in_maximum_packing_example_t_no_compatible s hs_mem_powerset hs_pw
  exact hs_not_clique hs_nclique.1
