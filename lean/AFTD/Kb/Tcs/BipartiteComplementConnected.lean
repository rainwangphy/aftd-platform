import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# bipartite_complement_connected

Topic: graphs   Node: b3331309e977

Provenance: helper lemma. step towards bipartite_complement_regular_spectrum_and_lambda2

Let H be an s-regular bipartite simple graph on parts V and W of size m ≥ 2. If 2s < m, then the bipartite complement G = K_{V,W} \ E(H) is connected.
-/

open scoped Classical in
/-- If H is an s-regular bipartite simple graph on parts V and W of size m ≥ 2 with 2s < m, then its bipartite complement K_{V,W} \ H is connected. -/
theorem bipartite_complement_connected
    {V W : Type*} [Fintype V] [Fintype W]
    (m s : ℕ) (hm : 2 ≤ m) (hV : Fintype.card V = m) (hW : Fintype.card W = m)
    (H : SimpleGraph (V ⊕ W)) (hH_sub : H ≤ completeBipartiteGraph V W)
    (hH_reg : H.IsRegularOfDegree s)
    (hs : 2 * s < m) :
    (completeBipartiteGraph V W \ H).Connected := by
  have hnl : ∀ v v', ¬ H.Adj (Sum.inl v) (Sum.inl v') := by
    intro v v' h
    have := hH_sub h
    simp at this
  have hnr : ∀ w w', ¬ H.Adj (Sum.inr w) (Sum.inr w') := by
    intro w w' h
    have := hH_sub h
    simp at this
  have hrow : ∀ i, ∑ j, H.adjMatrix ℝ i j = s := by
    intro i
    have := SimpleGraph.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) hH_reg (a := 1) (v := i)
    simp only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one] at this
    exact this
  have hcardL : ∀ v, (Finset.univ.filter fun w => H.Adj (Sum.inl v) (Sum.inr w)).card = s := by
    intro v
    have h := hrow (Sum.inl v)
    rw [Fintype.sum_sum_type] at h
    simp only [SimpleGraph.adjMatrix_apply, hnl, if_false, Finset.sum_const_zero, zero_add,
      Finset.sum_boole] at h
    exact_mod_cast h
  have hcardR : ∀ w, (Finset.univ.filter fun v => H.Adj (Sum.inr w) (Sum.inl v)).card = s := by
    intro w
    have h := hrow (Sum.inr w)
    rw [Fintype.sum_sum_type] at h
    simp only [SimpleGraph.adjMatrix_apply, hnr, if_false, Finset.sum_const_zero, add_zero,
      Finset.sum_boole] at h
    exact_mod_cast h
  set G := completeBipartiteGraph V W \ H with hG
  have hGlr : ∀ v w, ¬ H.Adj (Sum.inl v) (Sum.inr w) → G.Adj (Sum.inl v) (Sum.inr w) := by
    intro v w h
    simp [hG, SimpleGraph.sdiff_adj, h]
  -- two left vertices are joined through a common non-neighbour
  have hLL : ∀ v v', G.Reachable (Sum.inl v) (Sum.inl v') := by
    intro v v'
    have hlt : ((Finset.univ.filter fun w => H.Adj (Sum.inl v) (Sum.inr w)) ∪
        (Finset.univ.filter fun w => H.Adj (Sum.inl v') (Sum.inr w))).card <
        (Finset.univ : Finset W).card := by
      refine lt_of_le_of_lt (Finset.card_union_le _ _) ?_
      rw [hcardL, hcardL, Finset.card_univ, hW]
      omega
    obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hw
    exact (hGlr v w hw.1).reachable.trans (hGlr v' w hw.2).reachable.symm
  have hR : ∀ w, ∃ v, G.Adj (Sum.inl v) (Sum.inr w) := by
    intro w
    have hlt : (Finset.univ.filter fun v => H.Adj (Sum.inr w) (Sum.inl v)).card <
        (Finset.univ : Finset V).card := by
      rw [hcardR, Finset.card_univ, hV]; omega
    obtain ⟨v, -, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact ⟨v, hGlr v w (fun h => hv h.symm)⟩
  obtain ⟨v0⟩ : Nonempty V := by
    rw [← Fintype.card_pos_iff]; omega
  have hreach : ∀ x, G.Reachable (Sum.inl v0) x := by
    intro x
    rcases x with v | w
    · exact hLL v0 v
    · obtain ⟨v, hv⟩ := hR w
      exact (hLL v0 v).trans hv.reachable
  haveI : Nonempty (V ⊕ W) := ⟨Sum.inl v0⟩
  exact ⟨fun x y => (hreach x).symm.trans (hreach y)⟩
