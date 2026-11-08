import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.FiniteThreeSetStableMaximumPackingsCoverSupport
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.FiniteVertexFamilyEdgePackingCoverBridge
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.G

/-!
# simple_graph_stable_triangle_active_edge_in_maximum_packing

Topic: graphs   Node: f0452e810dc5

Provenance: helper lemma. Elementary packing exchange in the triangle packing-cover campaign; the packing definition is from arXiv:2610.15539, Section 1.

In a finite graph where deleting any edge preserves the maximum triangle packing number, every edge belonging to a triangle is used by some maximum triangle packing.
-/

lemma simple_graph_stable_triangle_active_edge_in_maximum_packing_edge_encoding_explicit
    {V : Type*} [DecidableEq V] (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    finite_vertex_set_edge_encoding ({x, y, z} : Finset V) = {s(x, y), s(y, z), s(x, z)} := by
  classical
  ext e
  induction' e using Sym2.inductionOn with u v
  simp only [finite_vertex_set_edge_encoding, Finset.mem_filter, Finset.mem_sym2_iff,
    Finset.mem_insert, Finset.mem_singleton, Sym2.mk_isDiag_iff, Sym2.eq,
    Sym2.rel_iff', Prod.mk.injEq]
  aesop

lemma simple_graph_stable_triangle_active_edge_in_maximum_packing_edge_encoding_card_three
    {V : Type*} [DecidableEq V] (t : Finset V) (ht : t.card = 3) :
    (finite_vertex_set_edge_encoding t).card = 3 := by
  classical
  rcases Finset.card_eq_three.mp ht with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  rw [simple_graph_stable_triangle_active_edge_in_maximum_packing_edge_encoding_explicit x y z hxy hxz hyz]
  have h1 : s(x, y) ≠ s(y, z) := by simp [Sym2.eq, Sym2.rel_iff']; aesop
  have h2 : s(x, y) ≠ s(x, z) := by simp [Sym2.eq, Sym2.rel_iff']; aesop
  have h3 : s(y, z) ≠ s(x, z) := by simp [Sym2.eq, Sym2.rel_iff']; aesop
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [h3]
  · simp [h1, h2]

lemma simple_graph_stable_triangle_active_edge_in_maximum_packing_subset_image_has_preimage
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (S : Finset α) (Q : Finset β) (hQ : Q ⊆ S.image f) :
    ∃ P : Finset α, P ⊆ S ∧ P.image f = Q ∧ P.card = Q.card := by
  classical
  have h_choice : ∀ b ∈ Q, ∃ a ∈ S, f a = b := by
    intro b hb
    have := hQ hb
    rw [Finset.mem_image] at this
    rcases this with ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  choose! g hg1 hg2 using h_choice
  set P := Q.attach.image (fun ⟨b, hb⟩ => g b hb)
  have hP_sub : P ⊆ S := by
    intro a ha
    rw [Finset.mem_image] at ha
    rcases ha with ⟨⟨b, hb⟩, -, rfl⟩
    exact hg1 b hb
  have hP_im : P.image f = Q := by
    ext b
    rw [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Finset.mem_image] at ha
      rcases ha with ⟨⟨b', hb'⟩, -, rfl⟩
      rw [hg2 b' hb']
      exact hb'
    · intro hb
      refine ⟨g b hb, ?_, hg2 b hb⟩
      rw [Finset.mem_image]
      exact ⟨⟨b, hb⟩, Finset.mem_attach _ _, rfl⟩
  have hP_card : P.card = Q.card := by
    apply le_antisymm
    · have := Finset.card_image_le (s := Q.attach) (f := fun ⟨b, hb⟩ => g b hb)
      simp only [Finset.card_attach] at this
      exact this
    · rw [← hP_im]
      exact Finset.card_image_le
  exact ⟨P, hP_sub, hP_im, hP_card⟩

lemma simple_graph_stable_triangle_active_edge_in_maximum_packing_edge_of_mem_family
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (y : Sym2 V)
    (hy : y ∈ (simple_graph_triangle_edge_family G).biUnion id) :
    y ∈ G.edgeSet := by
  classical
  rw [Finset.mem_biUnion] at hy
  rcases hy with ⟨t, ht, hy_in_t⟩
  dsimp only [id] at hy_in_t
  unfold simple_graph_triangle_edge_family at ht
  rw [Finset.mem_image] at ht
  rcases ht with ⟨s, hs, rfl⟩
  rw [Finset.mem_filter] at hs
  obtain ⟨-, hclique⟩ := hs
  rw [finite_vertex_set_edge_encoding, Finset.mem_filter] at hy_in_t
  obtain ⟨h_sym2, h_nondiag⟩ := hy_in_t
  induction' y using Sym2.inductionOn with u v
  simp only [Sym2.mk_isDiag_iff] at h_nondiag
  simp only [Finset.mem_sym2_iff, Sym2.mem_iff] at h_sym2
  have hu : u ∈ s := h_sym2 u (Or.inl rfl)
  have hv : v ∈ s := h_sym2 v (Or.inr rfl)
  exact hclique.isClique hu hv h_nondiag

lemma simple_graph_stable_triangle_active_edge_in_maximum_packing_not_mem_encoding_of_clique_deleteEdges
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (y : Sym2 V) (t : Finset V)
    (ht : (G.deleteEdges {y}).IsNClique 3 t) :
    y ∉ finite_vertex_set_edge_encoding t := by
  classical
  intro hy
  rw [finite_vertex_set_edge_encoding, Finset.mem_filter] at hy
  obtain ⟨h_sym2, h_nondiag⟩ := hy
  induction' y using Sym2.inductionOn with u v
  simp only [Sym2.mk_isDiag_iff] at h_nondiag
  simp only [Finset.mem_sym2_iff, Sym2.mem_iff] at h_sym2
  have hu : u ∈ t := h_sym2 u (Or.inl rfl)
  have hv : v ∈ t := h_sym2 v (Or.inr rfl)
  have hadj : (G.deleteEdges {s(u, v)}).Adj u v := ht.isClique hu hv h_nondiag
  rw [SimpleGraph.deleteEdges_adj] at hadj
  simp at hadj

lemma simple_graph_stable_triangle_active_edge_in_maximum_packing_e_in_family_biUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet)
    (hactive : ∃ t : Finset V, G.IsNClique 3 t ∧ ∀ x ∈ e, x ∈ t) :
    e ∈ (simple_graph_triangle_edge_family G).biUnion id := by
  classical
  rcases hactive with ⟨t, ht, he_in_t⟩
  rw [Finset.mem_biUnion]
  refine ⟨finite_vertex_set_edge_encoding t, ?_, ?_⟩
  · unfold simple_graph_triangle_edge_family
    rw [Finset.mem_image]
    refine ⟨t, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ t, ht⟩
  · dsimp only [id]
    rw [finite_vertex_set_edge_encoding, Finset.mem_filter]
    refine ⟨?_, G.not_isDiag_of_mem_edgeSet he⟩
    induction' e using Sym2.inductionOn with u v
    simp only [Finset.mem_sym2_iff, Sym2.mem_iff]
    intro x hx
    exact he_in_t x (Sym2.mem_iff.mpr hx)

lemma simple_graph_stable_triangle_active_edge_in_maximum_packing_edge_subset_of_mem_encoding
    {V : Type*} [DecidableEq V]
    (t : Finset V) (e : Sym2 V)
    (he : e ∈ finite_vertex_set_edge_encoding t) :
    ∀ x ∈ e, x ∈ t := by
  classical
  rw [finite_vertex_set_edge_encoding, Finset.mem_filter, Finset.mem_sym2_iff] at he
  exact he.1

theorem simple_graph_stable_triangle_active_edge_in_maximum_packing
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hstable : ∀ e ∈ G.edgeSet,
      simple_graph_triangle_packing_number (G.deleteEdges {e}) =
        simple_graph_triangle_packing_number G)
    (e : Sym2 V) (he : e ∈ G.edgeSet)
    (hactive : ∃ t : Finset V, G.IsNClique 3 t ∧ ∀ x ∈ e, x ∈ t) :
    ∃ P : Finset (Finset V),
      (∀ t ∈ P, G.IsNClique 3 t) ∧
      (P : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧
      P.card = simple_graph_triangle_packing_number G ∧
      ∃ t ∈ P, ∀ x ∈ e, x ∈ t := by
  classical
  set k := simple_graph_triangle_packing_number G
  set F := simple_graph_triangle_edge_family G
  set T_all := (Finset.univ : Finset (Finset V)).filter (G.IsNClique 3)
  have hF_def : F = T_all.image finite_vertex_set_edge_encoding := rfl
  have hthree : ∀ t ∈ F, t.card = 3 := by
    intro t ht
    rw [hF_def, Finset.mem_image] at ht
    rcases ht with ⟨s, hs, rfl⟩
    rw [Finset.mem_filter] at hs
    exact simple_graph_stable_triangle_active_edge_in_maximum_packing_edge_encoding_card_three s hs.2.card_eq
  have hmax : ∀ P ⊆ F, (P : Set (Finset (Sym2 V))).Pairwise Disjoint → P.card ≤ k := by
    intro P hP hpw
    obtain ⟨T, hT_sub, hT_im, hT_card⟩ :=
      simple_graph_stable_triangle_active_edge_in_maximum_packing_subset_image_has_preimage
        finite_vertex_set_edge_encoding T_all P (by rw [← hF_def]; exact hP)
    have hsize : ∀ t ∈ T, 2 ≤ t.card := by
      intro t ht
      have := hT_sub ht
      rw [Finset.mem_filter] at this
      rw [this.2.card_eq]
      omega
    have hbridge := finite_vertex_family_edge_packing_cover_bridge T ∅ hsize (by simp)
    rw [hT_im] at hbridge
    have hT_pw : (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) := hbridge.2.1.mp hpw
    have hT_clique : ∀ t ∈ T, G.IsNClique 3 t := by
      intro t ht
      have := hT_sub ht
      rw [Finset.mem_filter] at this
      exact this.2
    have hbdd : BddAbove {n | ∃ T : Finset (Finset V), (∀ a ∈ T, G.IsNClique 3 a) ∧
        (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ T.card = n} := by
      refine ⟨(Finset.univ : Finset (Finset V)).card, ?_⟩
      rintro n ⟨T', -, -, rfl⟩
      exact Finset.card_le_univ T'
    have hle : T.card ≤ k := by
      change T.card ≤ simple_graph_triangle_packing_number G
      unfold simple_graph_triangle_packing_number
      exact le_csSup hbdd ⟨T, hT_clique, hT_pw, rfl⟩
    omega
  have hstab : ∀ y ∈ F.biUnion id, ∃ P ⊆ F,
      (P : Set (Finset (Sym2 V))).Pairwise Disjoint ∧ P.card = k ∧ ∀ s ∈ P, y ∉ s := by
    intro y hy
    have hye : y ∈ G.edgeSet := simple_graph_stable_triangle_active_edge_in_maximum_packing_edge_of_mem_family G y hy
    have hstab_y := hstable y hye
    set G' := G.deleteEdges {y}
    set P_set : Set ℕ := {n | ∃ T : Finset (Finset V), (∀ t ∈ T, G'.IsNClique 3 t) ∧
      (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ T.card = n}
    have hbdd' : BddAbove P_set := by
      refine ⟨(Finset.univ : Finset (Finset V)).card, ?_⟩
      rintro n ⟨T', -, -, rfl⟩
      exact Finset.card_le_univ T'
    have hne' : P_set.Nonempty := ⟨0, ∅, by simp, by simp, rfl⟩
    obtain ⟨T, hT_clique, hT_pw, hT_c⟩ := Nat.sSup_mem hne' hbdd'
    have hT_card_eq : T.card = k := by
      have hs : sSup P_set = simple_graph_triangle_packing_number G' := rfl
      rw [hT_c, hs, hstab_y]
    have hsize : ∀ t ∈ T, 2 ≤ t.card := by
      intro t ht
      rw [(hT_clique t ht).card_eq]
      omega
    set P' := T.image finite_vertex_set_edge_encoding
    have hbridge := finite_vertex_family_edge_packing_cover_bridge T ∅ hsize (by simp)
    refine ⟨P', ?_, ?_, ?_, ?_⟩
    · intro F' hF'
      rw [Finset.mem_image] at hF'
      rcases hF' with ⟨t, ht, rfl⟩
      rw [hF_def, Finset.mem_image]
      refine ⟨t, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ t, ?_⟩
      have ht_cl := hT_clique t ht
      exact ⟨ht_cl.1.mono (G.deleteEdges_le {y}), ht_cl.2⟩
    · exact hbridge.2.1.mpr hT_pw
    · rw [hbridge.1, hT_card_eq]
    · intro s hs
      rw [Finset.mem_image] at hs
      rcases hs with ⟨t, ht, rfl⟩
      exact simple_graph_stable_triangle_active_edge_in_maximum_packing_not_mem_encoding_of_clique_deleteEdges G y t (hT_clique t ht)
  have he_in : e ∈ F.biUnion id := simple_graph_stable_triangle_active_edge_in_maximum_packing_e_in_family_biUnion G e he hactive
  obtain ⟨Q, hQ_sub, hQ_pw, hQ_card, ⟨s, hs_in_Q, he_in_s⟩⟩ :=
    finite_three_set_stable_maximum_packings_cover_support F k hthree hmax hstab e he_in
  obtain ⟨P, hP_sub, hP_im, hP_card⟩ :=
    simple_graph_stable_triangle_active_edge_in_maximum_packing_subset_image_has_preimage
      finite_vertex_set_edge_encoding T_all Q (by rw [← hF_def]; exact hQ_sub)
  have hsize : ∀ t ∈ P, 2 ≤ t.card := by
    intro t ht
    have := hP_sub ht
    rw [Finset.mem_filter] at this
    rw [this.2.card_eq]
    omega
  have hbridge := finite_vertex_family_edge_packing_cover_bridge P ∅ hsize (by simp)
  rw [hP_im] at hbridge
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have := hP_sub ht
    rw [Finset.mem_filter] at this
    exact this.2
  · exact hbridge.2.1.mp hQ_pw
  · rw [hP_card, hQ_card]
  · rw [← hP_im, Finset.mem_image] at hs_in_Q
    rcases hs_in_Q with ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    exact simple_graph_stable_triangle_active_edge_in_maximum_packing_edge_subset_of_mem_encoding t e he_in_s
