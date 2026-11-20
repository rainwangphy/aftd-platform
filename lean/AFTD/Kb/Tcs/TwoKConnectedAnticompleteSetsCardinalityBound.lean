import AFTD.Prelude

/-!
# two_k_connected_anticomplete_sets_cardinality_bound

Topic: graphs   Node: da71dee585f2

Provenance: helper lemma. General multiple-cut counting ingredient in the OP-1957 campaign.

In a graph on 2k+d+3 vertices with no separator smaller than 2k, any two nonempty disjoint anticomplete vertex sets have combined size at most d+3.
-/

theorem two_k_connected_anticomplete_sets_cardinality_bound
    (k d : ℕ) (G : SimpleGraph (Fin (2 * k + d + 3)))
    (A B : Finset (Fin (2 * k + d + 3)))
    (hsep : ∀ C X Y : Finset (Fin (2 * k + d + 3)),
      X.Nonempty → Y.Nonempty → Disjoint C X → Disjoint C Y → Disjoint X Y →
      C ∪ X ∪ Y = Finset.univ →
      (∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) → 2 * k ≤ C.card)
    (hA : A.Nonempty) (hB : B.Nonempty) (hAB : Disjoint A B)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) : A.card + B.card ≤ d + 3 := by
  classical
  let C := (Finset.univ : Finset (Fin (2 * k + d + 3))) \ (A ∪ B)
  have hCA : Disjoint C A := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxA
    simp only [C, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or] at hxC
    exact hxC.1 hxA
  have hCB : Disjoint C B := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxB
    simp only [C, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or] at hxC
    exact hxC.2 hxB
  have hcover : C ∪ A ∪ B = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, C, Finset.mem_sdiff]
    by_cases hx : x ∈ A ∪ B
    · simp only [Finset.mem_union] at hx
      tauto
    · exact Or.inl (Or.inl ⟨trivial, by simpa only [Finset.mem_union] using hx⟩)
  have hcut := hsep C A B hA hB hCA hCB hAB hcover hcross
  have hcard : C.card + (A ∪ B).card = 2 * k + d + 3 := by
    dsimp [C]
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (A ∪ B))
  rw [Finset.card_union_of_disjoint hAB] at hcard
  omega
