import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberLeTwoOfPackingNumberLeOne

/-!
# simple_graph_five_pairwise_edge_intersecting_triangles_common_edge

Topic: graphs   Node: 716beb828af5

Provenance: helper lemma. Structural property of graph triangle families used in the triangle packing-cover campaign; see the pairwise-intersection cases in simple_graph_triangle_cover_number_le_two_of_packing_number_le_one and related local reductions in arXiv:2610.15269, Section 3.

If a finite family contains at least five distinct graph triangles and any two share an edge, then one graph edge belongs to every triangle in the family.
-/

private lemma simple_graph_five_pairwise_edge_intersecting_triangles_common_edge_inter_card_le_one_of_not_subset {V : Type*} [DecidableEq V] {s t : Finset V}
    (hs : s.card = 2) (hnot : ¬ s ⊆ t) : (s ∩ t).card ≤ 1 := by
  have hproper : s ∩ t ⊂ s := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    apply hnot
    intro x hx
    have hx' : x ∈ s ∩ t := by simpa [heq] using hx
    exact (Finset.mem_inter.mp hx').2
  have hlt := Finset.card_lt_card hproper
  omega

private lemma simple_graph_five_pairwise_edge_intersecting_triangles_common_edge_subset_union_of_not_subset {V : Type*} [DecidableEq V]
    (t0 t1 t : Finset V)
    (h01 : (t0 ∩ t1).card = 2)
    (ht : t.card = 3)
    (ht0 : 2 ≤ (t ∩ t0).card) (ht1 : 2 ≤ (t ∩ t1).card)
    (hnot : ¬ (t0 ∩ t1) ⊆ t) : t ⊆ t0 ∪ t1 := by
  let s := t0 ∩ t1
  let A := t ∩ t0
  let B := t ∩ t1
  have hAB_card : (A ∩ B).card ≤ 1 := by
    have hAB_eq : A ∩ B = t ∩ s := by
      ext x
      simp [A, B, s, and_assoc, and_left_comm, and_comm]
    rw [hAB_eq, Finset.inter_comm t s]
    exact simple_graph_five_pairwise_edge_intersecting_triangles_common_edge_inter_card_le_one_of_not_subset h01 hnot
  have hUnion_sub : A ∪ B ⊆ t := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).1
    · exact (Finset.mem_inter.mp hx).1
  have hUnion_card : (A ∪ B).card = 3 := by
    have hc : (A ∪ B).card = A.card + B.card - (A ∩ B).card := Finset.card_union A B
    have hAc : 2 ≤ A.card := ht0
    have hBc : 2 ≤ B.card := ht1
    have hle : (A ∪ B).card ≤ 3 := by
      simpa [ht] using Finset.card_le_card hUnion_sub
    omega
  have hUnion_eq : A ∪ B = t := by
    apply Finset.eq_of_subset_of_card_le hUnion_sub
    omega
  intro x hx
  have hx' : x ∈ A ∪ B := by rw [hUnion_eq]; exact hx
  rcases Finset.mem_union.mp hx' with hx' | hx'
  · exact Finset.mem_union_left _ (Finset.mem_inter.mp hx').2
  · exact Finset.mem_union_right _ (Finset.mem_inter.mp hx').2

private lemma simple_graph_five_pairwise_edge_intersecting_triangles_common_edge_subset_union_of_contains_s {V : Type*} [DecidableEq V]
    (t0 t1 t t2 : Finset V)
    (h01 : (t0 ∩ t1).card = 2)
    (ht : t.card = 3)
    (hst : t0 ∩ t1 ⊆ t)
    (ht2_sub : t2 ⊆ t0 ∪ t1)
    (hnot2 : ¬ (t0 ∩ t1) ⊆ t2)
    (hinter_t_t2 : 2 ≤ (t ∩ t2).card) :
    t ⊆ t0 ∪ t1 := by
  let s := t0 ∩ t1
  let U := t0 ∪ t1
  by_contra hnot_sub
  rw [Finset.not_subset] at hnot_sub
  rcases hnot_sub with ⟨x, hxt, hxU⟩
  have hsU : s ⊆ U := by
    intro y hy
    exact Finset.mem_union_left _ (Finset.mem_inter.mp hy).1
  have hx_not_s : x ∉ s := fun hx => hxU (hsU hx)
  have h_insert_sub : insert x s ⊆ t := by
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hys
    · exact hxt
    · exact hst hys
  have hinsert_card : (insert x s).card = 3 := by
    rw [Finset.card_insert_of_notMem hx_not_s, h01]
  have h_insert_eq : insert x s = t := by
    apply Finset.eq_of_subset_of_card_le h_insert_sub
    rw [ht, hinsert_card]
  have ht_sub : t ⊆ insert x s := by rw [h_insert_eq]
  have hx_not_t2 : x ∉ t2 := fun hx2 => hxU (ht2_sub hx2)
  have hsub_inter : t ∩ t2 ⊆ s ∩ t2 := by
    intro y hy
    rcases Finset.mem_inter.mp hy with ⟨hyt, hyt2⟩
    have hyins : y ∈ insert x s := ht_sub hyt
    rw [Finset.mem_insert] at hyins
    rcases hyins with rfl | hys
    · exact (hx_not_t2 hyt2).elim
    · exact Finset.mem_inter.mpr ⟨hys, hyt2⟩
  have hcard_le : (t ∩ t2).card ≤ (s ∩ t2).card := Finset.card_le_card hsub_inter
  have hs_inter_le : (s ∩ t2).card ≤ 1 := by
    exact simple_graph_five_pairwise_edge_intersecting_triangles_common_edge_inter_card_le_one_of_not_subset h01 hnot2
  omega

theorem simple_graph_five_pairwise_edge_intersecting_triangles_common_edge {V : Type*} [DecidableEq V] (G : SimpleGraph V) (T : Finset (Finset V)) (htri : ∀ t ∈ T, G.IsNClique 3 t) (hinter : (T : Set (Finset V)).Pairwise (fun s t => 2 ≤ (s ∩ t).card)) (hfive : 5 ≤ T.card) : ∃ e : Sym2 V, e ∈ G.edgeSet ∧ ∀ t ∈ T, ∀ v ∈ e, v ∈ t := by
  classical
  have hcard_all : ∀ t ∈ T, t.card = 3 := fun t ht => (htri t ht).card_eq
  obtain ⟨t0, ht0T, t1, ht1T, ht01ne⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
  have ht0_card : t0.card = 3 := hcard_all t0 ht0T
  have ht1_card : t1.card = 3 := hcard_all t1 ht1T
  have hs_card0 : (t0 ∩ t1).card = 2 := by
    have hge : 2 ≤ (t0 ∩ t1).card := hinter ht0T ht1T ht01ne
    have hle : (t0 ∩ t1).card ≤ 3 := by
      have := Finset.card_le_card (Finset.inter_subset_left : t0 ∩ t1 ⊆ t0)
      omega
    have hne : (t0 ∩ t1).card ≠ 3 := by
      intro h3
      have heq : t0 ∩ t1 = t0 := by
        apply Finset.eq_of_subset_of_card_le (Finset.inter_subset_left : t0 ∩ t1 ⊆ t0)
        omega
      have ht0sub : t0 ⊆ t1 := by
        intro x hx
        have hx' : x ∈ t0 ∩ t1 := by rw [heq]; exact hx
        exact (Finset.mem_inter.mp hx').2
      have ht0eq : t0 = t1 := by
        apply Finset.eq_of_subset_of_card_le ht0sub
        omega
      exact ht01ne ht0eq
    omega
  let s := t0 ∩ t1
  have hs_card : s.card = 2 := hs_card0
  have hU_card : (t0 ∪ t1).card = 4 := by
    rw [Finset.card_union, ht0_card, ht1_card, hs_card0]
  have hcommon : ∀ t ∈ T, s ⊆ t := by
    by_contra hnotcommon
    push Not at hnotcommon
    obtain ⟨t2, ht2T, ht2not⟩ := hnotcommon
    have ht2_ne_t0 : t2 ≠ t0 := by
      intro h
      apply ht2not
      rw [h]
      exact Finset.inter_subset_left
    have ht2_ne_t1 : t2 ≠ t1 := by
      intro h
      apply ht2not
      rw [h]
      exact Finset.inter_subset_right
    have h2_0 : 2 ≤ (t2 ∩ t0).card := hinter ht2T ht0T ht2_ne_t0
    have h2_1 : 2 ≤ (t2 ∩ t1).card := hinter ht2T ht1T ht2_ne_t1
    have ht2_sub : t2 ⊆ t0 ∪ t1 := by
      exact simple_graph_five_pairwise_edge_intersecting_triangles_common_edge_subset_union_of_not_subset t0 t1 t2 hs_card0 (hcard_all t2 ht2T) h2_0 h2_1 ht2not
    have hall_sub_U : ∀ t ∈ T, t ⊆ t0 ∪ t1 := by
      intro t htT
      by_cases hst : s ⊆ t
      · have ht_ne_t2 : t ≠ t2 := by
          intro h
          apply ht2not
          simpa [h] using hst
        have h2 : 2 ≤ (t ∩ t2).card := hinter htT ht2T ht_ne_t2
        exact simple_graph_five_pairwise_edge_intersecting_triangles_common_edge_subset_union_of_contains_s t0 t1 t t2 hs_card0 (hcard_all t htT) hst ht2_sub ht2not h2
      · have ht_ne_t0 : t ≠ t0 := by
          intro h
          apply hst
          rw [h]
          exact Finset.inter_subset_left
        have ht_ne_t1 : t ≠ t1 := by
          intro h
          apply hst
          rw [h]
          exact Finset.inter_subset_right
        have h0 : 2 ≤ (t ∩ t0).card := hinter htT ht0T ht_ne_t0
        have h1 : 2 ≤ (t ∩ t1).card := hinter htT ht1T ht_ne_t1
        exact simple_graph_five_pairwise_edge_intersecting_triangles_common_edge_subset_union_of_not_subset t0 t1 t hs_card0 (hcard_all t htT) h0 h1 hst
    have hT_sub : T ⊆ (t0 ∪ t1).powersetCard 3 := by
      intro t htT
      rw [Finset.mem_powersetCard]
      exact ⟨hall_sub_U t htT, hcard_all t htT⟩
    have hT_card_le : T.card ≤ 4 := by
      calc
        T.card ≤ ((t0 ∪ t1).powersetCard 3).card := Finset.card_le_card hT_sub
        _ = (t0 ∪ t1).card.choose 3 := Finset.card_powersetCard 3 (t0 ∪ t1)
        _ = 4 := by rw [hU_card]; norm_num
    omega
  obtain ⟨u, v, huv, hs_eq⟩ := Finset.card_eq_two.mp hs_card
  have hu_s : u ∈ s := by rw [hs_eq]; simp
  have hv_s : v ∈ s := by rw [hs_eq]; simp
  have hu_t0 : u ∈ t0 := hcommon t0 ht0T hu_s
  have hv_t0 : v ∈ t0 := hcommon t0 ht0T hv_s
  have hadj : G.Adj u v := by
    exact (htri t0 ht0T).isClique hu_t0 hv_t0 huv
  refine ⟨Sym2.mk u v, ?_, ?_⟩
  · rw [SimpleGraph.mem_edgeSet]
    exact hadj
  · intro t htT w hw
    rw [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl
    · exact hcommon t htT hu_s
    · exact hcommon t htT hv_s
