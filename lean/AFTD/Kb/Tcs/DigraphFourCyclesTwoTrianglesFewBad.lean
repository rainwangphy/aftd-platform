import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_four_cycles_two_triangles_few_bad

Topic: graphs   Node: bb0fee8b3e29

Provenance: helper lemma. Two-triangle deletion mechanism for OP-110, using the degree-defect two-cycle theorem DOI:10.1137/080715792 Theorem 3.

Suppose a finite loopless digraph has minimum outdegree at least seven and contains two disjoint directed triangles. If no outside vertex has six out-neighbors in their union, at most two outside vertices have five out-neighbors in their union, and the displayed robust two-cycle theorem holds on induced subsets, then the digraph contains four disjoint directed cycles.
-/

theorem digraph_four_cycles_two_triangles_few_bad
    (α : Type) [Fintype α] [DecidableEq α] [Nonempty α]
    (D : Digraph α) [DecidableRel D.Adj] (hloop : ∀ v, ¬ D.Adj v v)
    (hdeg : ∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hrobust : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      (T.filter fun v => (T.filter fun w => D.Adj v w).card = 2).card ≤ 2 →
      ∃ s : Fin 2 → Finset α, (∀ i, s i ⊆ T ∧ digraph_directed_cycle_on D (s i)) ∧
        Pairwise (fun i j => Disjoint (s i) (s j)))
    (C₁ C₂ : Finset α) (hC₁ : digraph_directed_cycle_on D C₁)
    (hC₂ : digraph_directed_cycle_on D C₂) (hdis : Disjoint C₁ C₂)
    (hcard₁ : C₁.card = 3) (hcard₂ : C₂.card = 3)
    (hnoall : ∀ v ∉ (C₁ ∪ C₂), ((C₁ ∪ C₂).filter fun w => D.Adj v w).card ≤ 5)
    (hfew : ((Finset.univ \ (C₁ ∪ C₂)).filter fun v =>
      5 ≤ ((C₁ ∪ C₂).filter fun w => D.Adj v w).card).card ≤ 2) :
    ∃ s : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) := by
  let U := C₁ ∪ C₂
  let T := Finset.univ \ U
  have hU : U.card = 6 := by
    simp [U, Finset.card_union_of_disjoint hdis, hcard₁, hcard₂]
  have hcover : ∀ x : α, x ∈ T ∨ x ∈ U := by
    intro x
    by_cases hx : x ∈ U
    · exact Or.inr hx
    · exact Or.inl (by simp [T, hx])
  have hT : T.Nonempty := by
    by_contra hn
    have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hs : (Finset.univ : Finset α) ⊆ U := by
      intro x hx
      rcases hcover x with h | h
      · rw [he] at h
        simp at h
      · exact h
    have hc := Finset.card_le_card hs
    obtain ⟨a⟩ := ‹Nonempty α›
    have hd := hdeg a
    have hdu := Finset.card_le_card (Finset.filter_subset (fun w => D.Adj a w) Finset.univ)
    omega
  have hsplit : ∀ x : α,
      (Finset.univ.filter fun w => D.Adj x w) ⊆
        (T.filter fun w => D.Adj x w) ∪ (U.filter fun w => D.Adj x w) := by
    intro x w hw
    have hadj := (Finset.mem_filter.mp hw).2
    rcases hcover w with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h, hadj⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h, hadj⟩)
  have hTdeg : ∀ x ∈ T, 2 ≤ (T.filter fun w => D.Adj x w).card := by
    intro x hx
    have hxU : x ∉ U := by simpa [T] using hx
    have h5 : (U.filter fun w => D.Adj x w).card ≤ 5 := hnoall x hxU
    have hc := Finset.card_le_card (hsplit x)
    have hu := Finset.card_union_le (T.filter fun w => D.Adj x w) (U.filter fun w => D.Adj x w)
    have hd := hdeg x
    omega
  have hbad : (T.filter fun v => (T.filter fun w => D.Adj v w).card = 2).card ≤ 2 := by
    have hs : (T.filter fun v => (T.filter fun w => D.Adj v w).card = 2) ⊆
        (T.filter fun v => 5 ≤ (U.filter fun w => D.Adj v w).card) := by
      intro x hx
      obtain ⟨hxT, hxdeg⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨hxT, ?_⟩
      have hc := Finset.card_le_card (hsplit x)
      have hu := Finset.card_union_le (T.filter fun w => D.Adj x w) (U.filter fun w => D.Adj x w)
      have hd := hdeg x
      omega
    have hh := Finset.card_le_card hs
    exact hh.trans hfew
  obtain ⟨t, ht, hpair⟩ := hrobust T hT hTdeg hbad
  have hdis₁ : ∀ i, Disjoint C₁ (t i) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro x hx hxt
    have hxT := (ht i).1 hxt
    have hxU : x ∉ U := by simpa [T] using hxT
    exact hxU (Finset.mem_union_left _ hx)
  have hdis₂ : ∀ i, Disjoint C₂ (t i) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro x hx hxt
    have hxT := (ht i).1 hxt
    have hxU : x ∉ U := by simpa [T] using hxT
    exact hxU (Finset.mem_union_right _ hx)
  let f : Fin 4 → Finset α := Fin.cases C₁ (Fin.cases C₂ t)
  refine ⟨f, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hC₁
    · exact hC₂
    · exact (ht 0).2
    · exact (ht 1).2
  · intro i j hij
    have ht01 := hpair (show (0 : Fin 2) ≠ 1 by decide)
    fin_cases i <;> fin_cases j <;>
      first
      | exact (hij rfl).elim
      | exact hdis
      | exact hdis.symm
      | exact hdis₁ 0
      | exact hdis₁ 1
      | exact (hdis₁ 0).symm
      | exact (hdis₁ 1).symm
      | exact hdis₂ 0
      | exact hdis₂ 1
      | exact (hdis₂ 0).symm
      | exact (hdis₂ 1).symm
      | exact ht01
      | exact ht01.symm
