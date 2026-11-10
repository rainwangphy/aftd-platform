import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphMaximumTrianglePackingEdgeMeets
import AFTD.Kb.Tcs.SimpleGraphPairStableSupportMaxK4AnchorInternal

/-!
# simple_graph_pair_stable_support_max_outside_link_card_le_packing

Topic: graphs   Node: 4c84d56fe08f

Provenance: helper lemma. The unique-owner step in state/campaigns/triangle_reductions/support_high_triangle_count_in701.md; compare outside-book exchanges in https://arxiv.org/abs/2308.16515.

For a support-maximal maximum triangle packing in a two-edge-stable graph, an outside vertex has at most one link edge per packed triangle. Thus the number of triangles containing it is at most the packing size.
-/

open scoped Sym2

lemma simple_graph_pair_stable_support_max_outside_link_card_le_packing_make_k4 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c x : Fin n) (s : Finset (Fin n)) (hs : s = {a, b, c})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcl : G.IsNClique 3 s)
    (hxs : x ∉ s)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hxc : G.Adj x c) :
    G.IsNClique 4 ({a, b, c, x} : Finset (Fin n)) := by
  have hax : a ≠ x := by rintro rfl; apply hxs; rw [hs]; simp
  have hbx : b ≠ x := by rintro rfl; apply hxs; rw [hs]; simp
  have hcx : c ≠ x := by rintro rfl; apply hxs; rw [hs]; simp
  have hclique_s := hcl.isClique
  rw [hs] at hclique_s
  refine ⟨?_, ?_⟩
  · intro u hu v hv huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.coe_insert, Finset.coe_singleton] at hu hv
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
    all_goals {
      first
      | contradiction
      | exact hxa | exact hxa.symm
      | exact hxb | exact hxb.symm
      | exact hxc | exact hxc.symm
      | { apply hclique_s <;> simp [hab, hac, hbc, huv] }
    }
  · have h1 : c ∉ ({x} : Finset (Fin n)) := by simp [hcx]
    have h2 : b ∉ ({c, x} : Finset (Fin n)) := by simp [hbc, hbx]
    have h3 : a ∉ ({b, c, x} : Finset (Fin n)) := by simp [hab, hac, hax]
    rw [Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1, Finset.card_singleton]

lemma simple_graph_pair_stable_support_max_outside_link_card_le_packing_edge_toFinset_inj
    {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {e1 e2 : Sym2 V} (he1 : e1 ∈ G.edgeFinset) (he2 : e2 ∈ G.edgeFinset)
    (h : e1.toFinset = e2.toFinset) : e1 = e2 := by
  induction' e1 using Sym2.inductionOn with u1 v1
  induction' e2 using Sym2.inductionOn with u2 v2
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he1 he2
  rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at h
  rw [Sym2.eq_iff]
  have hne1 := G.ne_of_adj he1
  have hne2 := G.ne_of_adj he2
  have hu1 : u1 ∈ ({u2, v2} : Finset V) := by rw [← h]; simp
  have hv1 : v1 ∈ ({u2, v2} : Finset V) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu1 hv1
  rcases hu1 with rfl | rfl <;> rcases hv1 with rfl | rfl
  · exact False.elim (hne1 rfl)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact False.elim (hne1 rfl)

lemma simple_graph_pair_stable_support_max_outside_link_card_le_packing_union_subsets
    {α : Type*} [DecidableEq α] (s V1 V2 : Finset α)
    (hs : s.card = 3) (h1 : V1 ⊆ s) (h2 : V2 ⊆ s)
    (hcard1 : V1.card = 2) (hcard2 : V2.card = 2)
    (hne : V1 ≠ V2) : V1 ∪ V2 = s := by
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.union_subset h1 h2
  · have : 2 < (V1 ∪ V2).card := by
      have : V1 ⊂ V1 ∪ V2 := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.subset_union_left, ?_⟩
        intro heq
        have : V2 ⊆ V1 := by
          intro x hx
          have : x ∈ V1 ∪ V2 := Finset.mem_union_right V1 hx
          rwa [← heq] at this
        have : V1 = V2 := by
          apply (Finset.eq_of_subset_of_card_le this _).symm
          rw [hcard1, hcard2]
        exact hne this
      have hc := Finset.card_lt_card this
      rwa [hcard1] at hc
    omega

theorem simple_graph_pair_stable_support_max_outside_link_card_le_packing (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hsupport : ∀ Q : Finset (Finset (Fin n)), (∀ t ∈ Q, G.IsNClique 3 t) → (Q : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1) → Q.card = P.card → (Q.biUnion id).card ≤ (P.biUnion id).card) (hmax : P.card = simple_graph_triangle_packing_number G) (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f → simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G) (x : Fin n) (hx : x ∉ P.biUnion id) : (G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v)).card ≤ P.card := by
  apply Finset.card_le_card_of_forall_subsingleton (r := fun e t => ∀ v ∈ e, v ∈ t)
  · intro e he
    have he_edge : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
    have he_adj : ∀ v ∈ e, G.Adj x v := (Finset.mem_filter.mp he).2
    induction' e using Sym2.inductionOn with u v
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he_edge
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at he_adj
    have huv : G.Adj u v := he_edge
    have hxu : G.Adj x u := he_adj.1
    have hxv : G.Adj x v := he_adj.2
    have hne_uv : u ≠ v := G.ne_of_adj huv
    have hne_ux : u ≠ x := (G.ne_of_adj hxu).symm
    have hne_vx : v ≠ x := (G.ne_of_adj hxv).symm
    have htri_uvx : G.IsNClique 3 ({u, v, x} : Finset (Fin n)) := by
      refine ⟨?_, ?_⟩
      · intro a ha b hb hab
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.coe_insert, Finset.coe_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        all_goals { first | contradiction | exact huv | exact huv.symm | exact hxu.symm | exact hxu | exact hxv.symm | exact hxv }
      · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [hne_vx]
        · simp [hne_uv, hne_ux]
    obtain ⟨s, hsP, hscard⟩ := simple_graph_maximum_triangle_packing_edge_meets G P htri hdisj hmax {u, v, x} htri_uvx
    refine ⟨s, hsP, ?_⟩
    have hxs : x ∉ s := by
      intro hxs
      apply hx
      rw [Finset.mem_biUnion]
      exact ⟨s, hsP, hxs⟩
    have hint : s ∩ ({u, v, x} : Finset (Fin n)) = s ∩ ({u, v} : Finset (Fin n)) := by
      ext a
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, rfl | rfl | rfl⟩
        · exact ⟨ha, Or.inl rfl⟩
        · exact ⟨ha, Or.inr rfl⟩
        · exact False.elim (hxs ha)
      · rintro ⟨ha, rfl | rfl⟩
        · exact ⟨ha, Or.inl rfl⟩
        · exact ⟨ha, Or.inr (Or.inl rfl)⟩
    rw [hint] at hscard
    have hsub : s ∩ ({u, v} : Finset (Fin n)) ⊆ {u, v} := Finset.inter_subset_right
    have hcard2 : ({u, v} : Finset (Fin n)).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp [hne_uv]
    have heq : s ∩ ({u, v} : Finset (Fin n)) = {u, v} := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [hcard2]
      exact hscard
    have hu : u ∈ s ∩ ({u, v} : Finset (Fin n)) := by rw [heq]; simp
    have hv : v ∈ s ∩ ({u, v} : Finset (Fin n)) := by rw [heq]; simp
    rw [Finset.mem_inter] at hu hv
    intro w hw
    simp only [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl
    · exact hu.1
    · exact hv.1
  · intro b hb e1 he1 e2 he2
    rcases he1 with ⟨he1_filt, he1_sub⟩
    rcases he2 with ⟨he2_filt, he2_sub⟩
    by_contra hne
    have he1_edge := (Finset.mem_filter.mp he1_filt).1
    have he2_edge := (Finset.mem_filter.mp he2_filt).1
    have hcard1 := SimpleGraph.card_toFinset_mem_edgeFinset (G := G) ⟨e1, he1_edge⟩
    have hcard2 := SimpleGraph.card_toFinset_mem_edgeFinset (G := G) ⟨e2, he2_edge⟩
    have hsub1 : e1.toFinset ⊆ b := by
      intro w hw
      exact he1_sub w (Sym2.mem_toFinset.mp hw)
    have hsub2 : e2.toFinset ⊆ b := by
      intro w hw
      exact he2_sub w (Sym2.mem_toFinset.mp hw)
    have hne_finset : e1.toFinset ≠ e2.toFinset := by
      intro h
      exact hne (simple_graph_pair_stable_support_max_outside_link_card_le_packing_edge_toFinset_inj G he1_edge he2_edge h)
    have hcl_b := htri b hb
    have hb_union := simple_graph_pair_stable_support_max_outside_link_card_le_packing_union_subsets b e1.toFinset e2.toFinset hcl_b.card_eq hsub1 hsub2 hcard1 hcard2 hne_finset
    have hadj_all : ∀ v ∈ b, G.Adj x v := by
      intro v hv
      rw [← hb_union] at hv
      simp only [Finset.mem_union] at hv
      rcases hv with hv1 | hv2
      · exact (Finset.mem_filter.mp he1_filt).2 v (Sym2.mem_toFinset.mp hv1)
      · exact (Finset.mem_filter.mp he2_filt).2 v (Sym2.mem_toFinset.mp hv2)
    obtain ⟨u, v, w, huv, huw, hvw, hb_eq⟩ := Finset.card_eq_three.mp hcl_b.card_eq
    have hu_in : u ∈ b := by rw [hb_eq]; simp
    have hv_in : v ∈ b := by rw [hb_eq]; simp
    have hw_in : w ∈ b := by rw [hb_eq]; simp
    have hxs : x ∉ b := by
      intro hxb
      apply hx
      rw [Finset.mem_biUnion]
      exact ⟨b, hb, hxb⟩
    have hk4 := simple_graph_pair_stable_support_max_outside_link_card_le_packing_make_k4 G u v w x b hb_eq huv huw hvw hcl_b hxs (hadj_all u hu_in) (hadj_all v hv_in) (hadj_all w hw_in)
    have hp : ({u, v, w} : Finset (Fin n)) ∈ P := by rw [← hb_eq]; exact hb
    have hx_in := simple_graph_pair_stable_support_max_k4_anchor_internal n G P htri hdisj hsupport hmax hstable u v w x hp hk4
    exact hx hx_in
