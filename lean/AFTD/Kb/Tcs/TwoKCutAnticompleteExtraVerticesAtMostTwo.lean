import AFTD.Prelude

/-!
# two_k_cut_anticomplete_extra_vertices_at_most_two

Topic: graphs   Node: a14fc42c01d0

Provenance: helper lemma. Endpoint multiplicity in the OP-1957 crossing-cut campaign.

In a graph on 2k+d+3 vertices with no separator smaller than 2k, suppose nonempty disjoint vertex sets Q and W are anticomplete and have |Q|+|W|=d+1. Any set P disjoint from Q and W whose vertices are all anticomplete to Q has at most two vertices.
-/

theorem two_k_cut_anticomplete_extra_vertices_at_most_two
    (k d : ℕ) (G : SimpleGraph (Fin (2 * k + d + 3)))
    (Q W P : Finset (Fin (2 * k + d + 3)))
    (hsep : ∀ C A B : Finset (Fin (2 * k + d + 3)),
      A.Nonempty → B.Nonempty → Disjoint C A → Disjoint C B → Disjoint A B →
      C ∪ A ∪ B = Finset.univ →
      (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) → 2 * k ≤ C.card)
    (hQ : Q.Nonempty) (hW : W.Nonempty) (hQW : Disjoint Q W)
    (hQP : Disjoint Q P) (hWP : Disjoint W P)
    (hsize : Q.card + W.card = d + 1)
    (hcross : ∀ q ∈ Q, ∀ z ∈ W ∪ P, ¬ G.Adj q z) : P.card ≤ 2 := by
  classical
  let C := (Finset.univ : Finset (Fin (2 * k + d + 3))) \ (Q ∪ (W ∪ P))
  have hQA : Disjoint Q (W ∪ P) := Finset.disjoint_union_right.mpr ⟨hQW, hQP⟩
  have hCQ : Disjoint C Q := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxQ
    simp only [C, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or] at hxC
    exact hxC.1 hxQ
  have hCA : Disjoint C (W ∪ P) := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxA
    simp only [C, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or] at hxC
    rcases Finset.mem_union.mp hxA with hxW | hxP
    · exact hxC.2.1 hxW
    · exact hxC.2.2 hxP
  have hcover : C ∪ Q ∪ (W ∪ P) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, C, Finset.mem_sdiff]
    by_cases hx : x ∈ Q ∪ (W ∪ P)
    · simp only [Finset.mem_union] at hx
      tauto
    · exact Or.inl (Or.inl ⟨trivial, by simpa only [Finset.mem_union] using hx⟩)
  have hcut := hsep C Q (W ∪ P) hQ (hW.mono Finset.subset_union_left) hCQ hCA hQA hcover hcross
  have hunion : (Q ∪ (W ∪ P)).card = Q.card + W.card + P.card := by
    rw [Finset.card_union_of_disjoint hQA, Finset.card_union_of_disjoint hWP]
    omega
  have hbound : (Q ∪ (W ∪ P)).card ≤ 2 * k + d + 3 := by
    simpa using Finset.card_le_univ (Q ∪ (W ∪ P))
  have hcard : C.card + (Q ∪ (W ∪ P)).card = 2 * k + d + 3 := by
    dsimp [C]
    simpa using Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (Q ∪ (W ∪ P)))
  omega
