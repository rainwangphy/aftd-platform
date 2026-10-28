import AFTD.Prelude

/-!
# complete_graph_odd_line_graph_indep_set_card_le

Topic: graphs   Node: b9e79cbe8345

Provenance: helper lemma. step towards complete_graph_odd_line_graph_le_chromaticNumber

In the line graph of K_n for odd n, every independent set of edges has cardinality at most (n - 1) / 2.
-/

theorem complete_graph_odd_line_graph_indep_set_card_le_fst_mem {V : Type*} (e : Sym2 V) :
    (Quot.out e).1 ∈ e := by
  have h := Sym2.mem_mk_left (Quot.out e).1 (Quot.out e).2
  have hq : s((Quot.out e).1, (Quot.out e).2) = e := by
    change Quot.mk (Sym2.Rel V) ((Quot.out e).1, (Quot.out e).2) = e
    rw [Prod.mk.eta]
    exact Quot.out_eq e
  rw [hq] at h
  exact h

theorem complete_graph_odd_line_graph_indep_set_card_le_snd_mem {V : Type*} (e : Sym2 V) :
    (Quot.out e).2 ∈ e := by
  have h := Sym2.mem_mk_right (Quot.out e).1 (Quot.out e).2
  have hq : s((Quot.out e).1, (Quot.out e).2) = e := by
    change Quot.mk (Sym2.Rel V) ((Quot.out e).1, (Quot.out e).2) = e
    rw [Prod.mk.eta]
    exact Quot.out_eq e
  rw [hq] at h
  exact h

theorem complete_graph_odd_line_graph_indep_set_card_le_ne {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) :
    (Quot.out e.val).1 ≠ (Quot.out e.val).2 := by
  have he := e.property
  have hq : Quot.mk (Sym2.Rel V) ((Quot.out e.val).1, (Quot.out e.val).2) = e.val := by
    rw [Prod.mk.eta]
    exact Quot.out_eq e.val
  rw [← hq] at he
  exact he.ne

theorem complete_graph_odd_line_graph_indep_set_card_le_fin2_cases (i1 i2 : Fin 2) (h : i1 ≠ i2) :
    (i1 = 0 ∧ i2 = 1) ∨ (i1 = 1 ∧ i2 = 0) := by
  fin_cases i1 <;> fin_cases i2
  · contradiction
  · left; exact ⟨rfl, rfl⟩
  · right; exact ⟨rfl, rfl⟩
  · contradiction

/-- In the line graph of K_n for odd n, every independent set of edges has cardinality at most (n - 1) / 2. -/
theorem complete_graph_odd_line_graph_indep_set_card_le (n : ℕ) (hodd : n % 2 = 1) (s : Finset (⊤ : SimpleGraph (Fin n)).edgeSet) (hs : (⊤ : SimpleGraph (Fin n)).lineGraph.IsIndepSet (s : Set (⊤ : SimpleGraph (Fin n)).edgeSet)) : s.card ≤ (n - 1) / 2 := by
  let f : Fin 2 × s → Fin n := fun p =>
    if p.1 = 0 then (Quot.out p.2.val.val).1 else (Quot.out p.2.val.val).2
  have hf : Function.Injective f := by
    intro ⟨i1, e1⟩ ⟨i2, e2⟩ h
    dsimp [f] at h
    have hm1 : (if i1 = 0 then (Quot.out e1.val.val).1 else (Quot.out e1.val.val).2) ∈ (e1.val.val : Sym2 (Fin n)) := by
      split_ifs
      · exact complete_graph_odd_line_graph_indep_set_card_le_fst_mem _
      · exact complete_graph_odd_line_graph_indep_set_card_le_snd_mem _
    have hm2 : (if i2 = 0 then (Quot.out e2.val.val).1 else (Quot.out e2.val.val).2) ∈ (e2.val.val : Sym2 (Fin n)) := by
      split_ifs
      · exact complete_graph_odd_line_graph_indep_set_card_le_fst_mem _
      · exact complete_graph_odd_line_graph_indep_set_card_le_snd_mem _
    have heq : e1.val = e2.val := by
      by_contra hne
      have hadj : (⊤ : SimpleGraph (Fin n)).lineGraph.Adj e1.val e2.val := by
        rw [SimpleGraph.lineGraph_adj_iff_exists]
        refine ⟨hne, ?_⟩
        exact ⟨_, hm1, h ▸ hm2⟩
      exact hs e1.prop e2.prop hne hadj
    have he : e1 = e2 := Subtype.ext heq
    subst he
    have hi : i1 = i2 := by
      by_contra hne
      have hcases := complete_graph_odd_line_graph_indep_set_card_le_fin2_cases i1 i2 hne
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [↓reduceIte, Fin.reduceEq] at h
        exact complete_graph_odd_line_graph_indep_set_card_le_ne ⊤ e1.val h
      · simp only [↓reduceIte, Fin.reduceEq] at h
        exact (complete_graph_odd_line_graph_indep_set_card_le_ne ⊤ e1.val h.symm).elim
    exact Prod.ext hi rfl
  have hle := Fintype.card_le_of_injective f hf
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Fintype.card_fin] at hle
  omega
