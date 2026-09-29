import AFTD.Prelude

/-!
# card_simpleGraph

Topic: combinatorics   Node: b37129802925

The number of simple graphs on a finite vertex set V is 2^{C(|V|,2)}, where C(|V|,2) = |V|(|V|-1)/2 is the number of unordered pairs of distinct vertices.
-/

/-- The number of simple graphs on a finite vertex set V is 2^{C(|V|,2)}. -/
theorem card_simpleGraph {V : Type*} [Fintype V] [DecidableEq V] :
    Fintype.card (SimpleGraph V) = 2 ^ (Fintype.card V).choose 2 := by
  have equiv : SimpleGraph V ≃ Set {e : Sym2 V // ¬ e.IsDiag} :=
  { toFun := fun G => {e | (e : Sym2 V) ∈ G.edgeSet}
    invFun := fun S => SimpleGraph.fromEdgeSet (Subtype.val '' S)
    left_inv := by
      intro G
      have hS : (Subtype.val '' {e : {e : Sym2 V // ¬ e.IsDiag} | (e : Sym2 V) ∈ G.edgeSet})
          = G.edgeSet := by
        ext x
        constructor
        · rintro ⟨e, he, rfl⟩; exact he
        · intro hx
          exact ⟨⟨x, G.not_isDiag_of_mem_edgeSet hx⟩, hx, rfl⟩
      simp only
      rw [hS, SimpleGraph.fromEdgeSet_edgeSet]
    right_inv := by
      intro S
      ext e
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        rw [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff] at h
        obtain ⟨h1, _⟩ := h
        rcases h1 with ⟨e', he', hval⟩
        have : e' = e := Subtype.ext hval
        rw [this] at he'
        exact he'
      · intro he
        rw [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff]
        refine ⟨?_, ?_⟩
        · exact ⟨e, he, rfl⟩
        · simpa [Sym2.mem_diagSet] using e.2 }
  rw [Fintype.card_congr equiv, Fintype.card_set, Sym2.card_subtype_not_diag]
