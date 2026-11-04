import AFTD.Prelude

/-!
# simple_graph_triangle_subset_of_separator

Topic: graphs   Node: ebebdf70d41c

Provenance: helper lemma. step towards simple_graph_triangle_cover_of_two_vertex_separator_induction

If vertex subsets A and B cover V and have no edges between A \ B and B \ A, then every triangle of G is contained entirely in A or entirely in B.
-/

/-- If vertex subsets A and B cover V and have no edges between A \ B and B \ A, then every triangle of G is contained entirely in A or entirely in B. -/
theorem simple_graph_triangle_subset_of_separator
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A B : Finset V)
    (hcover : A ∪ B = Finset.univ)
    (hcross : ∀ x ∈ A \ B, ∀ y ∈ B \ A, ¬ G.Adj x y)
    (t : Finset V) (ht : G.IsNClique 3 t) :
    t ⊆ A ∨ t ⊆ B := by
  by_contra h
  rw [not_or, Finset.not_subset, Finset.not_subset] at h
  obtain ⟨⟨x, hxt, hxA⟩, ⟨y, hyt, hyB⟩⟩ := h
  have hxB : x ∈ B := by
    have : x ∈ A ∪ B := hcover ▸ Finset.mem_univ x
    rcases Finset.mem_union.mp this with h | h
    · exact absurd h hxA
    · exact h
  have hyA : y ∈ A := by
    have : y ∈ A ∪ B := hcover ▸ Finset.mem_univ y
    rcases Finset.mem_union.mp this with h | h
    · exact h
    · exact absurd h hyB
  have hxy : y ≠ x := by
    rintro rfl
    exact hxA hyA
  have hadj : G.Adj y x := ht.1 hyt hxt hxy
  exact hcross y (Finset.mem_sdiff.mpr ⟨hyA, hyB⟩) x (Finset.mem_sdiff.mpr ⟨hxB, hxA⟩) hadj
