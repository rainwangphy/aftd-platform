import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMatchingNum
import AFTD.Kb.Tcs.GraphMatchingNumLeVertexCoverNum
import AFTD.Kb.Tcs.BipartiteHallStepIsVertexCover
import AFTD.Kb.Tcs.IsMatchingSupDisjointEncard

/-!
# konig_matching_vertex_cover_num

Topic: graphs   Node: 354cdc48c2d5

Provenance: formalization of a published result. Source: Diestel, Graph Theory, Theorem 2.1.1

König's theorem: in any finite bipartite simple graph G, the matching number is equal to the vertex cover number.
-/

/-- In a bipartite graph with sides `A`, `B`, the part `A ∩ C` of a minimum vertex cover `C` can be
matched injectively to neighbours in `B` outside `C` (the marriage condition holds by minimality). -/
theorem bipartite_min_cover_side_inj_neighbors {V : Type*} [Fintype V] (G : SimpleGraph V) (A B C : Set V)
    (hdisj : Disjoint A B)
    (hadj : ∀ ⦃v w⦄, G.Adj v w → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A))
    (hC : G.IsVertexCover C) (hmin : C.encard = G.vertexCoverNum) :
    ∃ F : V → V, Set.InjOn F (A ∩ C) ∧ ∀ a ∈ A ∩ C, F a ∈ B ∧ F a ∉ C ∧ G.Adj a (F a) := by
  classical
  let X : Finset V := Finset.univ.filter fun v => v ∈ A ∩ C
  let t : X → Finset V := fun a => Finset.univ.filter fun b => b ∈ B ∧ b ∉ C ∧ G.Adj a b
  have hX : ∀ v, v ∈ A ∩ C → v ∈ X := fun v hv => by simpa [X] using hv
  have hmarr : ∀ s : Finset X, s.card ≤ (s.biUnion t).card := by
    intro s
    by_contra hlt
    push Not at hlt
    let Sf : Finset V := s.map (Function.Embedding.subtype _)
    have hS : (Sf : Set V) ⊆ A ∩ C := by
      intro v hv
      obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hv)
      have := x.2
      simpa [X] using this
    have hcov := bipartite_hall_step_is_vertex_cover G A B C Sf hdisj hadj hC hS
    have hle := hcov.vertexCoverNum_le
    rw [← hmin] at hle
    let Cf : Finset V := Finset.univ.filter fun v => v ∈ C
    have hCe : C.encard = (Cf.card : ℕ∞) := by
      have hCf : C = (Cf : Set V) := by ext v; simp [Cf]
      rw [hCf, Set.encard_coe_eq_coe_finsetCard]
    have hsub : (C \ (Sf : Set V)) ∪ {b ∈ B \ C | ∃ a ∈ (Sf : Set V), G.Adj a b} ⊆
        (((Cf \ Sf) ∪ s.biUnion t : Finset V) : Set V) := by
      rintro v (⟨hvC, hvS⟩ | ⟨⟨hvB, hvC⟩, a, haS, hav⟩)
      · have : v ∈ Cf \ Sf := Finset.mem_sdiff.2 ⟨by simp [Cf, hvC], fun h => hvS (Finset.mem_coe.2 h)⟩
        exact Finset.mem_coe.2 (Finset.mem_union_left _ this)
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 haS)
        refine Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, hx, ?_⟩))
        simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hvB, hvC, hav⟩
    have h1 := Set.encard_le_encard hsub
    rw [Set.encard_coe_eq_coe_finsetCard] at h1
    have hSC : Sf ⊆ Cf := by
      intro v hv
      have := hS (Finset.mem_coe.2 hv)
      simp [Cf, this.2]
    have h2 := Finset.card_union_le (Cf \ Sf) (s.biUnion t)
    have h3 := Finset.card_sdiff_add_card_eq_card hSC
    have h4 : Sf.card = s.card := Finset.card_map _
    have h5 := le_trans hle h1
    rw [hCe] at h5
    norm_cast at h5
    omega
  obtain ⟨f, hfi, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hmarr
  refine ⟨fun v => if h : v ∈ X then f ⟨v, h⟩ else v, ?_, ?_⟩
  · intro a ha b hb hab
    dsimp only at hab
    rw [dif_pos (hX a ha), dif_pos (hX b hb)] at hab
    exact congrArg Subtype.val (hfi hab)
  · intro a ha
    dsimp only
    rw [dif_pos (hX a ha)]
    have := hft ⟨a, hX a ha⟩
    simpa [t] using this

/-- An injective choice of neighbours `a ↦ F a` on a finite set `P`, with `P` inside a set `D` and
every `F a` outside it, gives a matching with `|P|` edges on the vertices `P ∪ F(P)`. -/
theorem subgraph_matching_of_injOn_neighbors {V : Type*} (G : SimpleGraph V) (P D : Set V) (F : V → V)
    (hinj : Set.InjOn F P) (hadjF : ∀ a ∈ P, G.Adj a (F a))
    (hPD : P ⊆ D) (hFD : ∀ a ∈ P, F a ∉ D) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts ⊆ P ∪ F '' P ∧ M.edgeSet.encard = P.encard := by
  have hsep : ∀ a ∈ P, ∀ b ∈ P, F a ≠ b := fun a ha b hb h => hFD a ha (h ▸ hPD hb)
  let M : G.Subgraph :=
    { verts := P ∪ F '' P
      Adj := fun v w => ∃ a ∈ P, (v = a ∧ w = F a) ∨ (v = F a ∧ w = a)
      adj_sub := by
        rintro v w ⟨a, ha, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · rw [h1, h2]; exact hadjF a ha
        · rw [h1, h2]; exact (hadjF a ha).symm
      edge_vert := by
        rintro v w ⟨a, ha, ⟨h1, -⟩ | ⟨h1, -⟩⟩
        · rw [h1]; exact Or.inl ha
        · rw [h1]; exact Or.inr ⟨a, ha, rfl⟩
      symm := ⟨fun v w ⟨a, ha, h⟩ =>
        ⟨a, ha, h.symm.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)⟩⟩ }
  have hMadj : ∀ v w, M.Adj v w ↔ ∃ a ∈ P, (v = a ∧ w = F a) ∨ (v = F a ∧ w = a) :=
    fun v w => Iff.rfl
  refine ⟨M, ?_, subset_rfl, ?_⟩
  · rintro v (hv | ⟨a, ha, rfl⟩)
    · refine ⟨F v, (hMadj _ _).2 ⟨v, hv, Or.inl ⟨rfl, rfl⟩⟩, fun y hy => ?_⟩
      obtain ⟨a, ha, h⟩ := (hMadj _ _).1 hy
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2, h1]
      · exact absurd h1.symm (hsep a ha v hv)
    · refine ⟨a, (hMadj _ _).2 ⟨a, ha, Or.inr ⟨rfl, rfl⟩⟩, fun y hy => ?_⟩
      obtain ⟨b, hb, h⟩ := (hMadj _ _).1 hy
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h1 (hsep a ha b hb)
      · exact h2.trans (hinj hb ha h1.symm)
  · have hE : M.edgeSet = (fun a => s(a, F a)) '' P := by
      ext e
      induction e using Sym2.ind with
      | h v w =>
        rw [SimpleGraph.Subgraph.mem_edgeSet, hMadj, Set.mem_image]
        constructor
        · rintro ⟨a, ha, h⟩
          refine ⟨a, ha, ?_⟩
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        · rintro ⟨a, ha, he⟩
          refine ⟨a, ha, ?_⟩
          rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1.symm, h2.symm⟩
          · exact Or.inr ⟨h2.symm, h1.symm⟩
    rw [hE]
    refine Set.InjOn.encard_image fun a ha b hb hab => ?_
    rcases Sym2.eq_iff.1 hab with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1.symm (hsep b hb a ha)

/-- König's min-max theorem: the matching number equals the vertex cover number in any finite bipartite graph. -/
theorem konig_matching_vertex_cover_num {V : Type*} [Fintype V] (G : SimpleGraph V) (h : G.IsBipartite) :
    graph_matching_num G = G.vertexCoverNum := by
  classical
  refine le_antisymm (graph_matching_num_le_vertex_cover_num G) ?_
  obtain ⟨c⟩ := h
  obtain ⟨C, hCe, hC⟩ := G.vertexCoverNum_exists
  let A : Set V := {v | c v = 0}
  let B : Set V := {v | c v = 1}
  have h01 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  have hdisj : Disjoint A B := by
    refine Set.disjoint_left.2 fun v ha hb => ?_
    have h1 : c v = 0 := ha
    have h2 : c v = 1 := hb
    rw [h1] at h2
    exact absurd h2 (by decide)
  have hAB : ∀ v, v ∈ A ∨ v ∈ B := fun v => h01 (c v)
  have hadj : ∀ ⦃v w⦄, G.Adj v w → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A) := by
    intro v w hvw
    have hne := c.valid hvw
    rcases h01 (c v) with h1 | h1 <;> rcases h01 (c w) with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hne
  have hadj' : ∀ ⦃v w⦄, G.Adj v w → (v ∈ B ∧ w ∈ A) ∨ (v ∈ A ∧ w ∈ B) :=
    fun v w h => (hadj h).symm
  obtain ⟨FA, hFAi, hFA⟩ := bipartite_min_cover_side_inj_neighbors G A B C hdisj hadj hC hCe
  obtain ⟨FB, hFBi, hFB⟩ := bipartite_min_cover_side_inj_neighbors G B A C hdisj.symm hadj' hC hCe
  obtain ⟨MA, hMA, hvA, heA⟩ := subgraph_matching_of_injOn_neighbors G (A ∩ C) C FA hFAi
    (fun a ha => (hFA a ha).2.2) Set.inter_subset_right (fun a ha => (hFA a ha).2.1)
  obtain ⟨MB, hMB, hvB, heB⟩ := subgraph_matching_of_injOn_neighbors G (B ∩ C) C FB hFBi
    (fun a ha => (hFB a ha).2.2) Set.inter_subset_right (fun a ha => (hFB a ha).2.1)
  have hd : Disjoint MA.verts MB.verts := by
    refine Set.disjoint_left.2 fun v hva hvb => ?_
    rcases hvA hva with hv1 | ⟨a, ha, rfl⟩ <;> rcases hvB hvb with hv2 | ⟨b, hb, hv2⟩
    · exact Set.disjoint_left.1 hdisj hv1.1 hv2.1
    · exact (hFB b hb).2.1 (by rw [hv2]; exact hv1.2)
    · exact (hFA a ha).2.1 hv2.2
    · exact Set.disjoint_left.1 hdisj (by rw [← hv2]; exact (hFB b hb).1) (hFA a ha).1
  obtain ⟨hM, hcard⟩ := isMatching_sup_disjoint_encard MA MB hMA hMB hd
  have hCsplit : C = (A ∩ C) ∪ (B ∩ C) := by
    ext v
    constructor
    · intro hv
      rcases hAB v with h | h
      · exact Or.inl ⟨h, hv⟩
      · exact Or.inr ⟨h, hv⟩
    · rintro (⟨-, hv⟩ | ⟨-, hv⟩) <;> exact hv
  have hCdisj : Disjoint (A ∩ C) (B ∩ C) :=
    hdisj.mono Set.inter_subset_left Set.inter_subset_left
  calc G.vertexCoverNum = C.encard := hCe.symm
    _ = (A ∩ C).encard + (B ∩ C).encard := by rw [← Set.encard_union_eq hCdisj, ← hCsplit]
    _ = (MA ⊔ MB).edgeSet.encard := by rw [hcard, heA, heB]
    _ ≤ graph_matching_num G :=
      le_iSup₂ (f := fun (M : G.Subgraph) (_ : M.IsMatching) => M.edgeSet.encard) (MA ⊔ MB) hM
