import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# bipartite_well_covered_has_perfect_matching

Topic: graphs   Node: 239d461dbfaa

Provenance: helper lemma. step towards bipartite_well_covered_exists_perfect_matching_ravindra

Every finite connected well-covered bipartite graph G with at least 2 vertices has a perfect matching.
-/

open SimpleGraph in
/-- Hall's condition for one side of a well-covered bipartite graph: for `t` contained in a
maximum-cardinality independent side `A`, the neighbourhood of `t` is at least as large. -/
private lemma bipartite_well_covered_has_perfect_matching_hall_side
    {V : Type*} [Fintype V] {G : SimpleGraph V} {A B : Set V}
    (hAB : G.IsBipartiteWith A B) (hAind : G.IsIndepSet A) (hBind : G.IsIndepSet B)
    (hAmax : ∀ s : Set V, Maximal G.IsIndepSet s → s.ncard = A.ncard)
    (hcardAB : A.ncard = B.ncard) (t : Set V) (ht : t ⊆ A) :
    t.ncard ≤ (⋃ x ∈ t, G.neighborSet x).ncard := by
  classical
  set N : Set V := ⋃ x ∈ t, G.neighborSet x with hNdef
  have hNsub : N ⊆ B := by
    intro y hy
    simp only [hNdef, Set.mem_iUnion, exists_prop] at hy
    obtain ⟨x, hxt, hyx⟩ := hy
    rw [SimpleGraph.mem_neighborSet] at hyx
    rcases hAB.mem_of_adj hyx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd h1 (Set.disjoint_left.mp hAB.disjoint (ht hxt))
  have hIind : G.IsIndepSet (t ∪ (B \ N)) := by
    intro a ha b hb hab hadj
    rcases ha with ha | ⟨haB, haN⟩
    · rcases hb with hb | ⟨hbB, hbN⟩
      · exact hAind (ht ha) (ht hb) hab hadj
      · refine hbN ?_
        simp only [hNdef, Set.mem_iUnion, exists_prop]
        exact ⟨a, ha, by rwa [SimpleGraph.mem_neighborSet]⟩
    · rcases hb with hb | ⟨hbB, hbN⟩
      · refine haN ?_
        simp only [hNdef, Set.mem_iUnion, exists_prop]
        exact ⟨b, hb, by rw [SimpleGraph.mem_neighborSet]; exact hadj.symm⟩
      · exact hBind haB hbB hab hadj
  have hSfin : {u : Set V | (t ∪ (B \ N)) ⊆ u ∧ G.IsIndepSet u}.Finite := Set.toFinite _
  obtain ⟨J, hJ⟩ := hSfin.exists_maximal ⟨t ∪ (B \ N), subset_refl _, hIind⟩
  have hJmax : Maximal G.IsIndepSet J := by
    refine ⟨hJ.1.2, ?_⟩
    intro u hu hJu
    exact hJ.2 ⟨Set.Subset.trans hJ.1.1 hJu, hu⟩ hJu
  have hJcard : J.ncard = A.ncard := hAmax J hJmax
  have hIle : (t ∪ (B \ N)).ncard ≤ J.ncard := Set.ncard_le_ncard hJ.1.1
  have hdisj : Disjoint t (B \ N) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact Set.disjoint_left.mp hAB.disjoint (ht hx) hx'.1
  have hNleB : N.ncard ≤ B.ncard := Set.ncard_le_ncard hNsub
  have hBN : (B \ N).ncard = B.ncard - N.ncard := Set.ncard_sdiff hNsub
  have hIunion : (t ∪ (B \ N)).ncard = t.ncard + (B \ N).ncard := Set.ncard_union_eq hdisj
  omega

/-- Every finite connected well-covered bipartite graph with at least 2 vertices has a perfect matching. -/
theorem bipartite_well_covered_has_perfect_matching {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected) (hbip : G.IsBipartite)
    (hcard : 2 ≤ Fintype.card V) (hwc : simple_graph_is_well_covered G) :
    ∃ M : SimpleGraph.Subgraph G, M.IsPerfectMatching := by
  classical
  haveI : G.LocallyFinite := fun v => (Set.toFinite _).fintype
  obtain ⟨C⟩ := hbip
  have htwo : ∀ x : Fin 2, x = 0 ∨ x = 1 := fun x => by fin_cases x <;> simp
  set A : Set V := C.colorClass 0 with hAdef
  set B : Set V := C.colorClass 1 with hBdef
  have hAB : G.IsBipartiteWith A B := by
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd (hx.symm.trans hx') (by decide)
    · intro v w hvw
      have hne := C.valid hvw
      have hv := htwo (C v)
      have hw := htwo (C w)
      rcases hv with h | h
      · refine Or.inl ⟨h, ?_⟩
        rcases hw with h' | h'
        · exact absurd (h.trans h'.symm) hne
        · exact h'
      · refine Or.inr ⟨h, ?_⟩
        rcases hw with h' | h'
        · exact h'
        · exact absurd (h.trans h'.symm) hne
  have hAind : G.IsIndepSet A := C.isIndepSet_colorClass 0
  have hBind : G.IsIndepSet B := C.isIndepSet_colorClass 1
  have hunion : A ∪ B = Set.univ := by
    ext v
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact htwo (C v)
  have hne : ∀ v : V, ∃ w, G.Adj v w := by
    intro v
    obtain ⟨w, hw⟩ : ∃ w, w ≠ v := by
      by_contra h
      push Not at h
      have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => by rw [h a, h b]
      omega
    have hr : G.Reachable v w := hconn.preconnected v w
    exact hr.elim fun p => by
      cases p with
      | nil => exact absurd rfl hw
      | cons h _ => exact ⟨_, h⟩
  have maxim : ∀ (P Q : Set V), G.IsBipartiteWith P Q → G.IsIndepSet P → P ∪ Q = Set.univ →
      Maximal G.IsIndepSet P := by
    intro P Q hPQ hPind hPQun
    rw [SimpleGraph.isMaximalIndepSet_iff]
    refine ⟨hPind, ?_⟩
    intro u hu hPu x hx
    by_contra hxP
    have hxQ : x ∈ Q := by
      have h : x ∈ P ∪ Q := by rw [hPQun]; trivial
      exact h.resolve_left hxP
    obtain ⟨w, hxw⟩ := hne x
    have hwP : w ∈ P := by
      rcases hPQ.mem_of_adj hxw with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 hxP
      · exact h2
    exact hu hx (hPu hwP) hxw.ne hxw
  have hAmaxS : Maximal G.IsIndepSet A := maxim A B hAB hAind hunion
  have hBmaxS : Maximal G.IsIndepSet B := by
    refine maxim B A hAB.symm hBind ?_
    rw [Set.union_comm]; exact hunion
  have hwcS : ∀ s t : Set V, Maximal G.IsIndepSet s → Maximal G.IsIndepSet t →
      s.ncard = t.ncard := by
    intro s t hs ht
    have hsfin : s.Finite := Set.toFinite s
    have htfin : t.Finite := Set.toFinite t
    have key : ∀ (u : Set V), (hufin : u.Finite) → Maximal G.IsIndepSet u →
        Maximal (fun v : Finset V => G.IsIndepSet (↑v : Set V)) hufin.toFinset := by
      intro u hufin hu
      have hcoe : (↑hufin.toFinset : Set V) = u := Set.Finite.coe_toFinset hufin
      refine ⟨?_, ?_⟩
      · show G.IsIndepSet (↑hufin.toFinset : Set V)
        rw [hcoe]; exact hu.1
      · intro w hw huw
        have h1 : u ⊆ (↑w : Set V) := by rw [← hcoe]; exact huw
        have h2 : (↑w : Set V) ⊆ u := hu.2 hw h1
        intro y hy
        rw [Set.Finite.mem_toFinset]
        exact h2 hy
    have h1 := key s hsfin hs
    have h2 := key t htfin ht
    have h := hwc hsfin.toFinset htfin.toFinset h1 h2
    rw [Set.ncard_eq_toFinset_card s hsfin, Set.ncard_eq_toFinset_card t htfin]
    exact h
  have hcardAB : A.ncard = B.ncard := hwcS A B hAmaxS hBmaxS
  have hAmax : ∀ s : Set V, Maximal G.IsIndepSet s → s.ncard = A.ncard :=
    fun s hs => hwcS s A hs hAmaxS
  have hBmax : ∀ s : Set V, Maximal G.IsIndepSet s → s.ncard = B.ncard :=
    fun s hs => hwcS s B hs hBmaxS
  refine SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le hAB ?_
  intro s
  have hdecomp : (⋃ x ∈ s, G.neighborSet x) =
      (⋃ x ∈ s ∩ A, G.neighborSet x) ∪ (⋃ x ∈ s ∩ B, G.neighborSet x) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_union, exists_prop]
    constructor
    · rintro ⟨x, hx, hy⟩
      rcases htwo (C x) with h | h
      · exact Or.inl ⟨x, ⟨hx, h⟩, hy⟩
      · exact Or.inr ⟨x, ⟨hx, h⟩, hy⟩
    · rintro (⟨x, ⟨hx, -⟩, hy⟩ | ⟨x, ⟨hx, -⟩, hy⟩)
      · exact ⟨x, hx, hy⟩
      · exact ⟨x, hx, hy⟩
  have hNdisj : Disjoint (⋃ x ∈ s ∩ A, G.neighborSet x)
      (⋃ x ∈ s ∩ B, G.neighborSet x) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop] at hy hy'
    obtain ⟨x, ⟨-, hx0⟩, hyx⟩ := hy
    obtain ⟨x', ⟨-, hx1⟩, hyx'⟩ := hy'
    rw [SimpleGraph.mem_neighborSet] at hyx hyx'
    have hy1 : y ∈ B := by
      rcases hAB.mem_of_adj hyx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · exact absurd h1 (Set.disjoint_left.mp hAB.disjoint hx0)
    have hy0 : y ∈ A := by
      rcases hAB.mem_of_adj hyx' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h1 (Set.disjoint_right.mp hAB.disjoint hx1)
      · exact h2
    exact Set.disjoint_left.mp hAB.disjoint hy0 hy1
  have hsdecomp : s = (s ∩ A) ∪ (s ∩ B) := by
    rw [← Set.inter_union_distrib_left, hunion, Set.inter_univ]
  have hsdisj : Disjoint (s ∩ A) (s ∩ B) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact Set.disjoint_left.mp hAB.disjoint hx.2 hx'.2
  have h1 : (s ∩ A).ncard ≤ (⋃ x ∈ s ∩ A, G.neighborSet x).ncard :=
    bipartite_well_covered_has_perfect_matching_hall_side hAB hAind hBind hAmax hcardAB _
      Set.inter_subset_right
  have h2 : (s ∩ B).ncard ≤ (⋃ x ∈ s ∩ B, G.neighborSet x).ncard :=
    bipartite_well_covered_has_perfect_matching_hall_side hAB.symm hBind hAind hBmax
      hcardAB.symm _ Set.inter_subset_right
  have hs_card : s.ncard = (s ∩ A).ncard + (s ∩ B).ncard := by
    conv_lhs => rw [hsdecomp]
    rw [Set.ncard_union_eq hsdisj]
  have hN_card : (⋃ x ∈ s, G.neighborSet x).ncard
      = (⋃ x ∈ s ∩ A, G.neighborSet x).ncard
        + (⋃ x ∈ s ∩ B, G.neighborSet x).ncard := by
    rw [hdecomp, Set.ncard_union_eq hNdisj]
  omega
