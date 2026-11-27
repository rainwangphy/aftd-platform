import AFTD.Prelude

/-!
# matching_four_switch_simplicial_complement_zero_codegree

Topic: graphs   Node: d9b94ce9ebb3

Provenance: helper lemma. OP-1957: four-switch at a simplicial complement vertex.

A perfect-matching edge uv lies on an alternating four-cycle if v has at least two neighbors, the complement neighbors of u form a clique, and u and v have no common complement neighbor.
-/

theorem matching_four_switch_simplicial_complement_zero_codegree
    {V : Type*} (G : SimpleGraph V) (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (u v : V) (huv : P.Adj u v)
    (hdeg : ∃ x y : V, x ≠ y ∧ G.Adj v x ∧ G.Adj v y)
    (hclique : ∀ a b : V, a ≠ b → (Gᶜ).Adj u a → (Gᶜ).Adj u b → (Gᶜ).Adj a b)
    (hsep : ∀ a : V, (Gᶜ).Adj u a → ¬ (Gᶜ).Adj v a) :
    ∃ a b : V, Function.Injective (![u,v,a,b] : Fin 4 → V) ∧ P.Adj a b ∧ G.Adj v a ∧ G.Adj u b := by
  have hP' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP
  obtain ⟨x, y, hxy, hvx, hvy⟩ := hdeg
  obtain ⟨w, hvw, hwu⟩ : ∃ w, G.Adj v w ∧ w ≠ u := by
    by_cases hx : x = u
    · exact ⟨y, hvy, fun h => hxy (hx.trans h.symm)⟩
    · exact ⟨x, hvx, hx⟩
  obtain ⟨z, hwz, -⟩ := hP' w
  have huv' : G.Adj u v := P.adj_sub huv
  have hwz' : G.Adj w z := P.adj_sub hwz
  have hwv : w ≠ v := (G.ne_of_adj hvw).symm
  have huv_ne : u ≠ v := G.ne_of_adj huv'
  have hwz_ne : w ≠ z := G.ne_of_adj hwz'
  -- z is not u or v: their mates are each other
  have hzu : z ≠ u := by
    rintro rfl
    have : w = v := ((hP' z).unique hwz.symm huv)
    exact hwv this
  have hzv : z ≠ v := by
    rintro rfl
    have : w = u := ((hP' z).unique hwz.symm huv.symm)
    exact hwu this
  have h1 := huv_ne.symm
  have h2 := hwu.symm
  have h3 := hwv.symm
  have h4 := hzu.symm
  have h5 := hzv.symm
  have h6 := hwz_ne.symm
  by_cases huz : G.Adj u z
  · refine ⟨w, z, ?_, hwz, hvw, huz⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      exact absurd hij ‹_›
  · have hcuz : (Gᶜ).Adj u z := by
      rw [SimpleGraph.compl_adj]; exact ⟨hzu.symm, huz⟩
    have hvz : G.Adj v z := by
      have := hsep z hcuz
      rw [SimpleGraph.compl_adj] at this
      push_neg at this
      exact this hzv.symm
    have huw : G.Adj u w := by
      by_contra huw
      have hcuw : (Gᶜ).Adj u w := by
        rw [SimpleGraph.compl_adj]; exact ⟨hwu.symm, huw⟩
      have := hclique w z hwz_ne hcuw hcuz
      rw [SimpleGraph.compl_adj] at this
      exact this.2 hwz'
    refine ⟨z, w, ?_, hwz.symm, hvz, huw⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      exact absurd hij ‹_›
