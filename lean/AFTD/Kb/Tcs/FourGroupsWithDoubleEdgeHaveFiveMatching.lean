import AFTD.Prelude
import AFTD.Kb.Tcs.IndexedDisjointCrossEdgesFormMatching

/-!
# four_groups_with_double_edge_have_five_matching

Topic: graphs   Node: e2bb262ad958

Provenance: helper lemma. Balanced-cut k=7 reduction for OP-1957; https://arxiv.org/abs/2611.22690.

Four disjoint vertex groups each containing an edge, one containing two disjoint edges, contain a five-edge matching.
-/

theorem four_groups_with_double_edge_have_five_matching
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (R : Finset V) (F : Fin 4 → Finset V)
    (hsub : ∀ i, F i ⊆ R)
    (hdis : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (hedge : ∀ i, ∃ a ∈ F i, ∃ b ∈ F i, G.Adj a b)
    (z : Fin 4) (a b c d : V)
    (ha : a ∈ F z) (hb : b ∈ F z) (hc : c ∈ F z) (hd : d ∈ F z)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts ⊆ (R : Set V) ∧ M.edgeSet.ncard=5 := by
  set_option maxHeartbeats 4000000 in
    classical
    choose a' ha' b' hb' hab' using hedge
    let f : Fin 4 → V := fun i => if i=z then a else a' i
    let g : Fin 4 → V := fun i => if i=z then b else b' i
    have hfi : ∀ i, f i ∈ F i := by
      intro i
      by_cases hi : i=z
      · subst i; simpa [f] using ha
      · simpa [f,hi] using ha' i
    have hgi : ∀ i, g i ∈ F i := by
      intro i
      by_cases hi : i=z
      · subst i; simpa [g] using hb
      · simpa [g,hi] using hb' i
    have hfg : ∀ i, G.Adj (f i) (g i) := by
      intro i
      by_cases hi : i=z
      · subst i; simpa [f,g] using hab
      · simpa [f,g,hi] using hab' i
    have hf : Function.Injective f := by
      intro i j he
      by_contra hij
      exact Finset.disjoint_left.mp (hdis i j hij) (hfi i) (he.symm ▸ hfi j)
    have hg : Function.Injective g := by
      intro i j he
      by_contra hij
      exact Finset.disjoint_left.mp (hdis i j hij) (hgi i) (he.symm ▸ hgi j)
    have hcross : ∀ i j, f i ≠ g j := by
      intro i j he
      by_cases hij : i=j
      · subst j
        exact G.ne_of_adj (hfg i) he
      · exact Finset.disjoint_left.mp (hdis i j hij) (hfi i) (he.symm ▸ hgi j)
    have hforbid : ∀ i, f i ≠ c ∧ f i ≠ d ∧ g i ≠ c ∧ g i ≠ d := by
      intro i
      by_cases hi : i=z
      · subst i
        simpa [f,g] using ⟨hac,had,hbc,hbd⟩
      · have hn : ∀ x ∈ F i, x ≠ c ∧ x ≠ d := by
          intro x hx
          constructor
          · intro he
            exact Finset.disjoint_left.mp (hdis i z hi) hx (he.symm ▸ hc)
          · intro he
            exact Finset.disjoint_left.mp (hdis i z hi) hx (he.symm ▸ hd)
        exact ⟨(hn (f i) (hfi i)).1,(hn (f i) (hfi i)).2,
          (hn (g i) (hgi i)).1,(hn (g i) (hgi i)).2⟩
    let ff : Fin 5 → V := Fin.snoc f c
    let gg : Fin 5 → V := Fin.snoc g d
    have hff : Function.Injective ff := by
      apply Fin.snoc_injective_of_injective hf
      rintro ⟨i,hi⟩
      exact (hforbid i).1 hi
    have hgg : Function.Injective gg := by
      apply Fin.snoc_injective_of_injective hg
      rintro ⟨i,hi⟩
      exact (hforbid i).2.2.2 hi
    have hcross5 : ∀ i j, ff i ≠ gg j := by
      intro i j
      induction i using Fin.lastCases with
      | cast i =>
        induction j using Fin.lastCases with
        | cast j => simpa [ff,gg] using hcross i j
        | last =>
          simp only [ff,gg,Fin.snoc_castSucc,Fin.snoc_last]
          exact (hforbid i).2.1
      | last =>
        induction j using Fin.lastCases with
        | cast j =>
          simp only [ff,gg,Fin.snoc_castSucc,Fin.snoc_last]
          exact (hforbid j).2.2.1.symm
        | last =>
          change c ≠ d
          exact G.ne_of_adj hcd
    have hadj5 : ∀ i, G.Adj (ff i) (gg i) := by
      intro i
      induction i using Fin.lastCases with
      | cast i => simpa [ff,gg] using hfg i
      | last =>
        change G.Adj c d
        exact hcd
    obtain ⟨M,hM,hMcard,hMverts⟩ := indexed_disjoint_cross_edges_form_matching G 5 ff gg hff hgg hcross5 hadj5
    refine ⟨M,hM,?_,hMcard⟩
    intro v hv
    rw [hMverts] at hv
    rcases hv with ⟨i,hi⟩ | ⟨i,hi⟩
    · induction i using Fin.lastCases with
      | cast i => exact hi ▸ hsub i (by simpa [ff] using hfi i)
      | last => exact hi ▸ hsub z hc
    · induction i using Fin.lastCases with
      | cast i => exact hi ▸ hsub i (by simpa [gg] using hgi i)
      | last => exact hi ▸ hsub z hd
