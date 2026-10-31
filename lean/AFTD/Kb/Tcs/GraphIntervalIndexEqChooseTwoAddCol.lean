import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIntervalIndex
import AFTD.Kb.Tcs.GraphCol
import AFTD.Kb.Tcs.GraphCollinearMiddleUnique

/-!
# graph_interval_index_eq_choose_two_add_col

Topic: graphs   Node: f344e17f8407

Provenance: formalization of a published result. Source: arXiv:2610.39966 Lemma 4

For every connected finite graph G on n vertices, the interval index Int(G) equals (n choose 2) + col(G).
-/

open scoped Classical

def graph_interval_index_eq_choose_two_add_col_P2 (V : Type*) [Fintype V] : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter (·.card = 2)

noncomputable def graph_interval_index_eq_choose_two_add_col_I {V : Type*} [Fintype V]
    (G : SimpleGraph V) (uv : Finset V) : Finset V :=
  Finset.univ.filter (fun w => ∀ u ∈ uv, ∀ v ∈ uv, u ≠ v → G.dist u w + G.dist w v = G.dist u v)

noncomputable def graph_interval_index_eq_choose_two_add_col_T {V : Type*} [Fintype V]
    (G : SimpleGraph V) (uv : Finset V) : Finset (Finset V) :=
  (graph_interval_index_eq_choose_two_add_col_I G uv \ uv).image (fun w => insert w uv)

theorem graph_interval_index_eq_choose_two_add_col_card_T {V : Type*} [Fintype V]
    (G : SimpleGraph V) (uv : Finset V) :
    (graph_interval_index_eq_choose_two_add_col_T G uv).card =
      (graph_interval_index_eq_choose_two_add_col_I G uv \ uv).card := by
  apply Finset.card_image_of_injOn
  intro w1 hw1 w2 hw2 heq
  rw [Finset.mem_coe, Finset.mem_sdiff] at hw1 hw2
  dsimp at heq
  have h_sdiff (w : V) (hw : w ∉ uv) : (insert w uv) \ uv = {w} := by
    ext x; simp [hw]
  have h1 := h_sdiff w1 hw1.2
  have h2 := h_sdiff w2 hw2.2
  rw [heq] at h1
  rw [h1] at h2
  exact Finset.singleton_inj.mp h2

theorem graph_interval_index_eq_choose_two_add_col_T_pairwise_disjoint {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) :
    (graph_interval_index_eq_choose_two_add_col_P2 V : Set (Finset V)).PairwiseDisjoint
      (graph_interval_index_eq_choose_two_add_col_T G) := by
  intro uv1 huv1 uv2 huv2 hne
  rw [Function.onFun, Finset.disjoint_iff_ne]
  rintro s hs1 _ hs2 rfl
  simp only [graph_interval_index_eq_choose_two_add_col_T, Finset.mem_image] at hs1 hs2
  rcases hs1 with ⟨w1, hw1, rfl⟩
  rcases hs2 with ⟨w2, hw2, heq⟩
  rw [Finset.mem_sdiff] at hw1 hw2
  have huv1_card : uv1.card = 2 := (Finset.mem_filter.mp huv1).2
  have huv2_card : uv2.card = 2 := (Finset.mem_filter.mp huv2).2
  by_cases hw : w1 = w2
  · subst hw
    have : uv1 = uv2 := by
      have h1 : (insert w1 uv1) \ {w1} = uv1 := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; aesop
      have h2 : (insert w1 uv2) \ {w1} = uv2 := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; aesop
      rw [← h1, ← heq, h2]
    exact hne this
  · have hw2_in_uv1 : w2 ∈ uv1 := by
      have : w2 ∈ insert w2 uv2 := Finset.mem_insert_self w2 uv2
      rw [heq] at this
      simp only [Finset.mem_insert] at this
      cases this with
      | inl h => exact (hw h.symm).elim
      | inr h => exact h
    have hw1_in_uv2 : w1 ∈ uv2 := by
      have : w1 ∈ insert w1 uv1 := Finset.mem_insert_self w1 uv1
      rw [← heq] at this
      simp only [Finset.mem_insert] at this
      cases this with
      | inl h => exact (hw h).elim
      | inr h => exact h
    obtain ⟨t, ht_uv1, ht_ne_w2⟩ : ∃ t ∈ uv1, t ≠ w2 := by
      rcases Finset.card_eq_two.mp huv1_card with ⟨a, b, hab, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw2_in_uv1
      rcases hw2_in_uv1 with rfl | rfl
      · exact ⟨b, by simp, hab.symm⟩
      · exact ⟨a, by simp, hab⟩
    have ht_ne_w1 : t ≠ w1 := by
      rintro rfl
      exact hw1.2 ht_uv1
    have ht_in_uv2 : t ∈ uv2 := by
      have : t ∈ insert w1 uv1 := Finset.mem_insert_of_mem ht_uv1
      rw [← heq] at this
      simp only [Finset.mem_insert] at this
      cases this with
      | inl h => exact (ht_ne_w2 h).elim
      | inr h => exact h
    have hw1_I : w1 ∈ graph_interval_index_eq_choose_two_add_col_I G uv1 := hw1.1
    dsimp [graph_interval_index_eq_choose_two_add_col_I] at hw1_I
    rw [Finset.mem_filter] at hw1_I
    have h_w1_dist := hw1_I.2 w2 hw2_in_uv1 t ht_uv1 (Ne.symm ht_ne_w2)
    have hw2_I : w2 ∈ graph_interval_index_eq_choose_two_add_col_I G uv2 := hw2.1
    dsimp [graph_interval_index_eq_choose_two_add_col_I] at hw2_I
    rw [Finset.mem_filter] at hw2_I
    have h_w2_dist := hw2_I.2 w1 hw1_in_uv2 t ht_in_uv2 ht_ne_w1.symm
    have h_uniq := @graph_collinear_middle_unique V G hG w1 w2 t hw ht_ne_w2.symm ht_ne_w1.symm h_w2_dist
    exact h_uniq h_w1_dist

theorem graph_interval_index_eq_choose_two_add_col_biUnion_T_eq {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    (graph_interval_index_eq_choose_two_add_col_P2 V).biUnion
      (graph_interval_index_eq_choose_two_add_col_T G) =
      (Finset.univ : Finset (Finset V)).filter (fun s =>
        s.card = 3 ∧ ∃ y ∈ s, ∃ x ∈ s, ∃ z ∈ s, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ G.dist x y + G.dist y z = G.dist x z) := by
  ext s
  simp only [Finset.mem_biUnion, graph_interval_index_eq_choose_two_add_col_P2,
             graph_interval_index_eq_choose_two_add_col_T,
             Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_sdiff]
  constructor
  · intro h
    rcases h with ⟨uv, huv2, w, ⟨hwI, hw_not_in⟩, rfl⟩
    have h_two := Finset.card_eq_two.mp huv2
    rcases h_two with ⟨x, z, hxz, huv_eq⟩
    have hcard : (insert w uv).card = 3 := by
      rw [Finset.card_insert_of_notMem hw_not_in, huv2]
    have hx_uv : x ∈ uv := by rw [huv_eq]; simp
    have hz_uv : z ∈ uv := by rw [huv_eq]; simp
    have hw_ne_x : w ≠ x := by rintro rfl; exact hw_not_in hx_uv
    have hw_ne_z : w ≠ z := by rintro rfl; exact hw_not_in hz_uv
    refine ⟨hcard, w, Finset.mem_insert_self w _, x, Finset.mem_insert_of_mem hx_uv, z,
            Finset.mem_insert_of_mem hz_uv, hw_ne_x.symm, hw_ne_z, hxz, ?_⟩
    dsimp [graph_interval_index_eq_choose_two_add_col_I] at hwI
    rw [Finset.mem_filter] at hwI
    exact hwI.2 x hx_uv z hz_uv hxz
  · rintro ⟨hcard, y, hy, x, hx, z, hz, hxy, hyz, hxz, hdist⟩
    refine ⟨{x, z}, Finset.card_pair hxz, y, ⟨?_, ?_⟩, ?_⟩
    · dsimp [graph_interval_index_eq_choose_two_add_col_I]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ y, ?_⟩
      intro u hu v hv huv_ne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · contradiction
      · exact hdist
      · rw [SimpleGraph.dist_comm (u := u) (v := y), SimpleGraph.dist_comm (u := y) (v := v),
            SimpleGraph.dist_comm (u := u) (v := v), add_comm]
        exact hdist
      · contradiction
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl
      · exact hxy.symm rfl
      · exact hyz rfl
    · have hsub : (insert y {x, z} : Finset V) ⊆ s := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl <;> assumption
      have h3 : (insert y {x, z} : Finset V).card = 3 := by
        have hy_not : y ∉ ({x, z} : Finset V) := by simp [hxy.symm, hyz]
        rw [Finset.card_insert_of_notMem hy_not, Finset.card_pair hxz]
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard, h3])

theorem graph_interval_index_eq_choose_two_add_col_I_card_sub_one {V : Type*} [Fintype V]
    (G : SimpleGraph V) (uv : Finset V) (huv : uv ∈ graph_interval_index_eq_choose_two_add_col_P2 V) :
    (graph_interval_index_eq_choose_two_add_col_I G uv).card - 1 =
      1 + (graph_interval_index_eq_choose_two_add_col_I G uv \ uv).card := by
  have huv2 : uv.card = 2 := (Finset.mem_filter.mp huv).2
  have hsub : uv ⊆ graph_interval_index_eq_choose_two_add_col_I G uv := by
    intro w hw
    dsimp [graph_interval_index_eq_choose_two_add_col_I]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro u hu v hv huv_ne
    obtain rfl | rfl : w = u ∨ w = v := by
      rcases Finset.card_eq_two.mp huv2 with ⟨x, y, hxy, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw hu hv
      aesop
    · rw [SimpleGraph.dist_self, zero_add]
    · rw [SimpleGraph.dist_self, add_zero]
  have hcard : (graph_interval_index_eq_choose_two_add_col_I G uv).card =
      (graph_interval_index_eq_choose_two_add_col_I G uv \ uv).card + 2 := by
    rw [← huv2]
    exact (Finset.card_sdiff_add_card_eq_card hsub).symm
  omega

theorem graph_interval_index_eq_choose_two_add_col_card_P2 (V : Type*) [Fintype V] :
    (graph_interval_index_eq_choose_two_add_col_P2 V).card = (Fintype.card V).choose 2 := by
  have : graph_interval_index_eq_choose_two_add_col_P2 V = Finset.powersetCard 2 Finset.univ := by
    ext s; simp [graph_interval_index_eq_choose_two_add_col_P2, Finset.mem_powersetCard]
  rw [this, Finset.card_powersetCard, Finset.card_univ]

/-- The interval index of a connected graph equals (n choose 2) plus the number of collinear triples (Lemma 4). -/
theorem graph_interval_index_eq_choose_two_add_col {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) :
    graph_interval_index G = (Fintype.card V).choose 2 + graph_col G := by
  have h_int : graph_interval_index G = (Fintype.card V).choose 2 +
      ∑ uv ∈ graph_interval_index_eq_choose_two_add_col_P2 V,
        (graph_interval_index_eq_choose_two_add_col_I G uv \ uv).card := by
    unfold graph_interval_index
    change (∑ uv ∈ graph_interval_index_eq_choose_two_add_col_P2 V,
      ((graph_interval_index_eq_choose_two_add_col_I G uv).card - 1)) =
      (Fintype.card V).choose 2 +
      ∑ uv ∈ graph_interval_index_eq_choose_two_add_col_P2 V,
        (graph_interval_index_eq_choose_two_add_col_I G uv \ uv).card
    have h1 : (∑ uv ∈ graph_interval_index_eq_choose_two_add_col_P2 V,
        ((graph_interval_index_eq_choose_two_add_col_I G uv).card - 1)) =
        ∑ uv ∈ graph_interval_index_eq_choose_two_add_col_P2 V,
          (1 + (graph_interval_index_eq_choose_two_add_col_I G uv \ uv).card) := by
      apply Finset.sum_congr rfl
      intro uv huv
      exact graph_interval_index_eq_choose_two_add_col_I_card_sub_one G uv huv
    rw [h1, Finset.sum_add_distrib]
    simp [graph_interval_index_eq_choose_two_add_col_card_P2]
  have h_col : graph_col G = ∑ uv ∈ graph_interval_index_eq_choose_two_add_col_P2 V,
      (graph_interval_index_eq_choose_two_add_col_I G uv \ uv).card := by
    unfold graph_col
    rw [← graph_interval_index_eq_choose_two_add_col_biUnion_T_eq]
    rw [Finset.card_biUnion (graph_interval_index_eq_choose_two_add_col_T_pairwise_disjoint G hG)]
    apply Finset.sum_congr rfl
    intro uv huv
    exact graph_interval_index_eq_choose_two_add_col_card_T G uv
  rw [h_int, h_col]
