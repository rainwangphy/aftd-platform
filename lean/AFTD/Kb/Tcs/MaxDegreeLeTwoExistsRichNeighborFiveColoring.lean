import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoringOfForallRich

/-!
# maxDegree_le_two_exists_rich_neighbor_five_coloring

Topic: graphs   Node: 76ec1e62f64d

Provenance: helper lemma. step towards subcubic_three_vertices_max_degree_le_one_exists_rich_neighbor_five_coloring

Every finite simple graph of maximum degree at most 2 admits a rich-neighbor 5-edge-colouring.
-/

open SimpleGraph

theorem maxDegree_le_two_exists_rich_neighbor_five_coloring_greedy_finset {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ)
    (hdeg : ∀ v : V, ∃ s : Finset V, G.neighborSet v ⊆ s ∧ s.card ≤ d)
    (S : Finset V) :
    ∃ f : (v : V) → v ∈ S → Fin (d + 1),
      ∀ (u : V) (hu : u ∈ S) (v : V) (hv : v ∈ S), G.Adj u v → f u hu ≠ f v hv := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun v hv => False.elim (by simp at hv), ?_⟩
    intro u hu; simp at hu
  | @insert a s ha ih =>
    obtain ⟨f, hf⟩ := ih
    obtain ⟨sa, hsa, hcard⟩ := hdeg a
    let bad_nodes := s.filter (fun x => x ∈ sa)
    let bad_colors : Finset (Fin (d + 1)) :=
      bad_nodes.attach.image (fun ⟨w, hw⟩ => f w (Finset.mem_of_mem_filter w hw))
    have hbn_sub : bad_nodes ⊆ sa := fun x hx => (Finset.mem_filter.mp hx).2
    have hbad_card : bad_colors.card ≤ d := by
      calc bad_colors.card
        _ ≤ bad_nodes.attach.card := Finset.card_image_le
        _ = bad_nodes.card := Finset.card_attach
        _ ≤ sa.card := Finset.card_le_card hbn_sub
        _ ≤ d := hcard
    have hex : ∃ c : Fin (d + 1), c ∉ bad_colors := by
      by_contra! h
      have hcard_le : (Finset.univ : Finset (Fin (d + 1))).card ≤ bad_colors.card := by
        apply Finset.card_le_card
        intro x _
        exact h x
      rw [Finset.card_univ, Fintype.card_fin] at hcard_le
      omega
    obtain ⟨c, hc⟩ := hex
    let f_ext : (v : V) → v ∈ insert a s → Fin (d + 1) := fun v hv =>
      if hva : v = a then c
      else f v ((Finset.mem_insert.mp hv).resolve_left hva)
    refine ⟨f_ext, ?_⟩
    intro u hu v hv hadj
    change (if hua : u = a then c else f u ((Finset.mem_insert.mp hu).resolve_left hua)) ≠
           (if hva : v = a then c else f v ((Finset.mem_insert.mp hv).resolve_left hva))
    split_ifs with hua hva hva
    · subst hua hva; exact (G.ne_of_adj hadj rfl).elim
    · subst hua
      have hvm : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hva
      intro heq
      apply hc
      rw [Finset.mem_image]
      have hv_sa : v ∈ sa := hsa hadj
      have hv_bn : v ∈ bad_nodes := Finset.mem_filter.mpr ⟨hvm, hv_sa⟩
      refine ⟨⟨v, hv_bn⟩, Finset.mem_attach _ _, ?_⟩
      exact heq.symm
    · subst hva
      have hum : u ∈ s := (Finset.mem_insert.mp hu).resolve_left hua
      intro heq
      apply hc
      rw [Finset.mem_image]
      have hu_sa : u ∈ sa := hsa (G.adj_symm hadj)
      have hu_bn : u ∈ bad_nodes := Finset.mem_filter.mpr ⟨hum, hu_sa⟩
      refine ⟨⟨u, hu_bn⟩, Finset.mem_attach _ _, ?_⟩
      exact heq
    · exact hf u _ v _ hadj

theorem maxDegree_le_two_exists_rich_neighbor_five_coloring_greedy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ)
    (hdeg : ∀ v : V, ∃ s : Finset V, G.neighborSet v ⊆ s ∧ s.card ≤ d) :
    Nonempty (G.Coloring (Fin (d + 1))) := by
  obtain ⟨f, hf⟩ := maxDegree_le_two_exists_rich_neighbor_five_coloring_greedy_finset G d hdeg Finset.univ
  exact ⟨Coloring.mk (fun v => f v (Finset.mem_univ v)) (fun hadj => hf _ _ _ _ hadj)⟩

def maxDegree_le_two_exists_rich_neighbor_five_coloring_aux_graph {V : Type*} (G : SimpleGraph V) :
    SimpleGraph G.edgeSet where
  Adj f g := f ≠ g ∧ (G.lineGraph.Adj f g ∨ ∃ e : G.edgeSet, G.lineGraph.Adj e f ∧ G.lineGraph.Adj e g)
  symm := ⟨by
    rintro f g ⟨hne, h | ⟨e, hef, heg⟩⟩
    · exact ⟨hne.symm, Or.inl (G.lineGraph.adj_symm h)⟩
    · exact ⟨hne.symm, Or.inr ⟨e, heg, hef⟩⟩⟩
  loopless := ⟨by
    intro f ⟨hne, _⟩
    exact hne rfl⟩

instance maxDegree_le_two_exists_rich_neighbor_five_coloring_decRelLineGraphAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableRel G.lineGraph.Adj := by
  intro e₁ e₂
  rw [lineGraph_adj_iff_exists]
  infer_instance

lemma maxDegree_le_two_exists_rich_neighbor_five_coloring_lineGraph_degree_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : G.maxDegree ≤ 2) (e : G.edgeSet) :
    ((Finset.univ : Finset G.edgeSet).filter (G.lineGraph.Adj e)).card ≤ 2 := by
  rcases e with ⟨val, hval⟩
  obtain ⟨u, v⟩ := val
  have hadj : G.Adj u v := hval
  have hcard_u : ((G.neighborFinset u).erase v).card ≤ 1 := by
    have h1 : v ∈ G.neighborFinset u := by simpa using hadj
    have h2 : ((G.neighborFinset u).erase v).card = (G.neighborFinset u).card - 1 :=
      Finset.card_erase_of_mem h1
    rw [h2]
    have h3 : (G.neighborFinset u).card ≤ 2 := by
      calc (G.neighborFinset u).card = G.degree u := rfl
      _ ≤ G.maxDegree := G.degree_le_maxDegree u
      _ ≤ 2 := hdeg
    omega
  have hcard_v : ((G.neighborFinset v).erase u).card ≤ 1 := by
    have h1 : u ∈ G.neighborFinset v := by simpa using hadj.symm
    have h2 : ((G.neighborFinset v).erase u).card = (G.neighborFinset v).card - 1 :=
      Finset.card_erase_of_mem h1
    rw [h2]
    have h3 : (G.neighborFinset v).card ≤ 2 := by
      calc (G.neighborFinset v).card = G.degree v := rfl
      _ ≤ G.maxDegree := G.degree_le_maxDegree v
      _ ≤ 2 := hdeg
    omega
  let im_u : Finset G.edgeSet :=
    ((G.neighborFinset u).erase v).attach.image (fun ⟨w, hw⟩ =>
      ⟨s(u, w), (G.mem_neighborFinset u w).mp (Finset.mem_of_mem_erase hw)⟩)
  let im_v : Finset G.edgeSet :=
    ((G.neighborFinset v).erase u).attach.image (fun ⟨w, hw⟩ =>
      ⟨s(v, w), (G.mem_neighborFinset v w).mp (Finset.mem_of_mem_erase hw)⟩)
  have hsub : (Finset.univ.filter (G.lineGraph.Adj ⟨s(u, v), hval⟩)) ⊆ im_u ∪ im_v := by
    intro ⟨val', hval'⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [lineGraph_adj_iff_exists] at hmem
    obtain ⟨hne, x, hx_e, hx_e'⟩ := hmem
    simp only [Sym2.mem_iff] at hx_e
    rcases hx_e with hxu | hxv
    · subst x
      rw [Finset.mem_union]
      left
      obtain ⟨a, b⟩ := val'
      simp only [Sym2.mem_iff] at hx_e'
      rcases hx_e' with hua | hub
      · have : a = u := hua.symm; subst a
        have h_adj_ub : G.Adj u b := hval'
        have h_b_ne_v : b ≠ v := by
          rintro rfl
          apply hne
          exact Subtype.ext rfl
        have hb_mem : b ∈ (G.neighborFinset u).erase v := by
          rw [Finset.mem_erase, G.mem_neighborFinset]
          exact ⟨h_b_ne_v, h_adj_ub⟩
        rw [Finset.mem_image]
        refine ⟨⟨b, hb_mem⟩, Finset.mem_attach _ _, ?_⟩
        exact Subtype.ext rfl
      · have : b = u := hub.symm; subst b
        have h_adj_ua : G.Adj u a := hval'.symm
        have h_a_ne_v : a ≠ v := by
          rintro rfl
          apply hne
          exact Subtype.ext (Sym2.eq_swap)
        have ha_mem : a ∈ (G.neighborFinset u).erase v := by
          rw [Finset.mem_erase, G.mem_neighborFinset]
          exact ⟨h_a_ne_v, h_adj_ua⟩
        rw [Finset.mem_image]
        refine ⟨⟨a, ha_mem⟩, Finset.mem_attach _ _, ?_⟩
        exact Subtype.ext (Sym2.eq_swap)
    · subst x
      rw [Finset.mem_union]
      right
      obtain ⟨a, b⟩ := val'
      simp only [Sym2.mem_iff] at hx_e'
      rcases hx_e' with hva | hvb
      · have : a = v := hva.symm; subst a
        have h_adj_vb : G.Adj v b := hval'
        have h_b_ne_u : b ≠ u := by
          rintro rfl
          apply hne
          exact Subtype.ext (Sym2.eq_swap)
        have hb_mem : b ∈ (G.neighborFinset v).erase u := by
          rw [Finset.mem_erase, G.mem_neighborFinset]
          exact ⟨h_b_ne_u, h_adj_vb⟩
        rw [Finset.mem_image]
        refine ⟨⟨b, hb_mem⟩, Finset.mem_attach _ _, ?_⟩
        exact Subtype.ext rfl
      · have : b = v := hvb.symm; subst b
        have h_adj_va : G.Adj v a := hval'.symm
        have h_a_ne_u : a ≠ u := by
          rintro rfl
          apply hne
          exact Subtype.ext rfl
        have ha_mem : a ∈ (G.neighborFinset v).erase u := by
          rw [Finset.mem_erase, G.mem_neighborFinset]
          exact ⟨h_a_ne_u, h_adj_va⟩
        rw [Finset.mem_image]
        refine ⟨⟨a, ha_mem⟩, Finset.mem_attach _ _, ?_⟩
        exact Subtype.ext (Sym2.eq_swap)
  change (Finset.univ.filter (G.lineGraph.Adj ⟨s(u, v), hval⟩)).card ≤ 2
  calc (Finset.univ.filter (G.lineGraph.Adj ⟨s(u, v), hval⟩)).card
    _ ≤ (im_u ∪ im_v).card := Finset.card_le_card hsub
    _ ≤ im_u.card + im_v.card := Finset.card_union_le im_u im_v
    _ ≤ ((G.neighborFinset u).erase v).card + ((G.neighborFinset v).erase u).card := by
      gcongr
      · calc im_u.card ≤ _ := Finset.card_image_le
        _ = _ := Finset.card_attach
      · calc im_v.card ≤ _ := Finset.card_image_le
        _ = _ := Finset.card_attach
    _ ≤ 1 + 1 := by omega
    _ = 2 := rfl

lemma maxDegree_le_two_exists_rich_neighbor_five_coloring_aux_graph_deg_le_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : G.maxDegree ≤ 2) (f : G.edgeSet) :
    ∃ s : Finset G.edgeSet,
      (maxDegree_le_two_exists_rich_neighbor_five_coloring_aux_graph G).neighborSet f ⊆ s ∧ s.card ≤ 4 := by
  let N1 := (Finset.univ : Finset G.edgeSet).filter (G.lineGraph.Adj f)
  have hN1 : N1.card ≤ 2 := maxDegree_le_two_exists_rich_neighbor_five_coloring_lineGraph_degree_le_two G hdeg f
  let N2 : G.edgeSet → Finset G.edgeSet := fun e =>
    ((Finset.univ : Finset G.edgeSet).filter (G.lineGraph.Adj e)).erase f
  have hN2 : ∀ e ∈ N1, (N2 e).card ≤ 1 := by
    intro e he
    have he_adj : G.lineGraph.Adj e f := by
      have := (Finset.mem_filter.mp he).2
      exact G.lineGraph.adj_symm this
    have hf_mem : f ∈ (Finset.univ : Finset G.edgeSet).filter (G.lineGraph.Adj e) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ f, he_adj⟩
    have := Finset.card_erase_of_mem hf_mem
    rw [this]
    have := maxDegree_le_two_exists_rich_neighbor_five_coloring_lineGraph_degree_le_two G hdeg e
    omega
  let s := N1 ∪ N1.biUnion N2
  refine ⟨s, ?_, ?_⟩
  · intro g hg
    simp only [mem_neighborSet] at hg
    rcases hg with ⟨hne, hadj | ⟨e, hef, heg⟩⟩
    · rw [Finset.mem_coe, Finset.mem_union]
      left
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ g, hadj⟩
    · rw [Finset.mem_coe, Finset.mem_union]
      right
      rw [Finset.mem_biUnion]
      have he_adj : G.lineGraph.Adj f e := G.lineGraph.adj_symm hef
      have he_in_N1 : e ∈ N1 := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ e, he_adj⟩
      refine ⟨e, he_in_N1, ?_⟩
      rw [Finset.mem_erase, Finset.mem_filter]
      exact ⟨hne.symm, Finset.mem_univ g, heg⟩
  · calc s.card
      _ ≤ N1.card + (N1.biUnion N2).card := Finset.card_union_le N1 _
      _ ≤ N1.card + ∑ e ∈ N1, (N2 e).card := by
        gcongr
        exact Finset.card_biUnion_le
      _ ≤ 2 + ∑ e ∈ N1, 1 := by
        gcongr
        exact hN2 _ ‹_›
      _ = 2 + N1.card := by simp
      _ ≤ 2 + 2 := by omega
      _ = 4 := rfl

/-- Base case of Lemma 2.2: any finite graph of maximum degree at most 2 admits a rich-neighbor 5-edge-coloring. -/
theorem maxDegree_le_two_exists_rich_neighbor_five_coloring {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : G.maxDegree ≤ 2) :
    ∃ c : G.lineGraph.Coloring (Fin 5), simple_graph_is_rich_neighbor_coloring G c := by
  obtain ⟨C⟩ := maxDegree_le_two_exists_rich_neighbor_five_coloring_greedy
    (maxDegree_le_two_exists_rich_neighbor_five_coloring_aux_graph G) 4
    (maxDegree_le_two_exists_rich_neighbor_five_coloring_aux_graph_deg_le_four G hdeg)
  have hc_valid : ∀ {f g : G.edgeSet}, G.lineGraph.Adj f g → C f ≠ C g := by
    intro f g hadj
    have hne : f ≠ g := G.lineGraph.ne_of_adj hadj
    have hadj_aux : (maxDegree_le_two_exists_rich_neighbor_five_coloring_aux_graph G).Adj f g := ⟨hne, Or.inl hadj⟩
    exact C.valid hadj_aux
  let c : G.lineGraph.Coloring (Fin 5) := Coloring.mk (fun e => C e) (fun hadj => hc_valid hadj)
  refine ⟨c, simple_graph_is_rich_neighbor_coloring_of_forall_rich G c ?_⟩
  intro e f g hef heg hfg
  have hadj_aux : (maxDegree_le_two_exists_rich_neighbor_five_coloring_aux_graph G).Adj f g := ⟨hfg, Or.inr ⟨e, hef, heg⟩⟩
  exact C.valid hadj_aux
