import AFTD.Prelude

/-!
# regular_bipartite_adj_charpoly_roots_contain_pm_degree

Topic: graphs   Node: 23c35a6ded23

Provenance: helper lemma. arXiv:2611.00591, Lemma 4.1 (step of its proof)

Let H be an s-regular graph contained in the complete bipartite graph on parts V, W of size m ≥ 1. Then s and −s are roots of the characteristic polynomial of the real adjacency matrix of H, with the multiset {s, −s} contained in its roots (so 0 has multiplicity at least 2 when s = 0).
-/

open scoped Classical in
theorem regular_bipartite_adj_charpoly_roots_contain_pm_degree
    {V W : Type*} [Fintype V] [Fintype W]
    (m s : ℕ) (hm : 1 ≤ m) (hV : Fintype.card V = m) (hW : Fintype.card W = m)
    (H : SimpleGraph (V ⊕ W)) (hH_sub : H ≤ completeBipartiteGraph V W)
    (hH_reg : H.IsRegularOfDegree s) :
    ({(s : ℝ), -(s : ℝ)} : Multiset ℝ) ≤ (H.adjMatrix ℝ).charpoly.roots := by
  have hnl : ∀ v v', ¬ H.Adj (Sum.inl v) (Sum.inl v') := by
    intro v v' h
    have := hH_sub h
    simp at this
  have hnr : ∀ w w', ¬ H.Adj (Sum.inr w) (Sum.inr w') := by
    intro w w' h
    have := hH_sub h
    simp at this
  set A := H.adjMatrix ℝ with hA
  have hll : ∀ v v', A (Sum.inl v) (Sum.inl v') = 0 := by
    intro v v'; rw [hA, SimpleGraph.adjMatrix_apply, if_neg (hnl v v')]
  have hrr : ∀ w w', A (Sum.inr w) (Sum.inr w') = 0 := by
    intro w w'; rw [hA, SimpleGraph.adjMatrix_apply, if_neg (hnr w w')]
  have hrow : ∀ i, ∑ j, A i j = s := by
    intro i
    have := SimpleGraph.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) hH_reg (a := 1) (v := i)
    simp only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one] at this
    exact this
  obtain ⟨v0⟩ : Nonempty V := by
    rw [← Fintype.card_pos_iff]; omega
  have hroot : ∀ μ : ℝ, ∀ u : V ⊕ W → ℝ, u (Sum.inl v0) ≠ 0 → A.mulVec u = μ • u →
      μ ∈ A.charpoly.roots := by
    intro μ u hu h
    rw [Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero, Polynomial.IsRoot,
      Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨u, fun h0 => hu (by rw [h0]; rfl), ?_⟩
    rw [Matrix.sub_mulVec, h]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hplus : (s : ℝ) ∈ A.charpoly.roots := by
    refine hroot s (fun _ => 1) (by norm_num) ?_
    ext i
    simp only [Matrix.mulVec, dotProduct, mul_one, Pi.smul_apply, smul_eq_mul]
    rw [hrow i]
  have hminus : -(s : ℝ) ∈ A.charpoly.roots := by
    refine hroot (-s) (Sum.elim (fun _ => 1) (fun _ => -1)) (by simp) ?_
    ext i
    have hrow' := hrow i
    rw [Fintype.sum_sum_type] at hrow'
    rcases i with v | w
    · simp only [hll, Finset.sum_const_zero, zero_add] at hrow'
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hll, hrow']
    · simp only [hrr, Finset.sum_const_zero, add_zero] at hrow'
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hrr, hrow']
  by_cases hs : s = 0
  · subst hs
    have hA0 : A = 0 := by
      ext i j
      rw [hA, SimpleGraph.adjMatrix_apply, if_neg]
      · rfl
      intro h
      have h1 : j ∈ H.neighborFinset i := (SimpleGraph.mem_neighborFinset _ _ _).mpr h
      have h2 : (H.neighborFinset i).card = 0 := hH_reg i
      rw [Finset.card_eq_zero] at h2
      rw [h2] at h1
      simp at h1
    rw [hA0, Matrix.charpoly_zero, Polynomial.roots_X_pow, Multiset.le_iff_count]
    intro a
    simp only [Fintype.card_sum, hV, hW, Multiset.count_nsmul, Nat.cast_zero, neg_zero,
      Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
    split_ifs <;> omega
  · have hne : (s : ℝ) ≠ -(s : ℝ) := by
      intro h
      have : (s : ℝ) = 0 := by linarith
      exact hs (by exact_mod_cast this)
    rw [Multiset.le_iff_subset]
    · intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hplus
      · exact hminus
    · rw [Multiset.insert_eq_cons, Multiset.nodup_cons]
      exact ⟨by simpa using hne, Multiset.nodup_singleton _⟩
