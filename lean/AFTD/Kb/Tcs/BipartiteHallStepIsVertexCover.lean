import AFTD.Prelude

/-!
# bipartite_hall_step_is_vertex_cover

Topic: graphs   Node: 63fca58d59c5

Provenance: helper lemma. step towards konig_matching_vertex_cover_num

In a bipartite graph with partition (A, B) and a vertex cover C, for any subset S of A ∩ C, the set (C \ S) ∪ (N(S) ∩ (B \ C)) is also a vertex cover of G.
-/

/-- In a bipartite graph, replacing a subset S of a vertex cover C in partition A with its neighbors in partition B outside C preserves the vertex cover property. -/
theorem bipartite_hall_step_is_vertex_cover {V : Type*} (G : SimpleGraph V) (A B C S : Set V)
    (hdisj : Disjoint A B)
    (hadj : ∀ ⦃v w⦄, G.Adj v w → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A))
    (hC : G.IsVertexCover C) (hS : S ⊆ A ∩ C) :
    G.IsVertexCover ((C \ S) ∪ {b ∈ B \ C | ∃ a ∈ S, G.Adj a b}) := by
  intro v w hvw
  have h_dir : ∀ {x y : V}, G.Adj x y → x ∈ A → y ∈ B →
      x ∈ (C \ S) ∪ {b ∈ B \ C | ∃ a ∈ S, G.Adj a b} ∨
      y ∈ (C \ S) ∪ {b ∈ B \ C | ∃ a ∈ S, G.Adj a b} := by
    intro x y hxy hxA hyB
    by_cases hyC : y ∈ C
    · right
      left
      exact ⟨hyC, fun hyS => Set.disjoint_iff.mp hdisj ⟨(hS hyS).1, hyB⟩⟩
    · have hxC : x ∈ C := (hC hxy).resolve_right hyC
      by_cases hxS : x ∈ S
      · right
        right
        exact ⟨⟨hyB, hyC⟩, x, hxS, hxy⟩
      · left
        left
        exact ⟨hxC, hxS⟩
  rcases hadj hvw with ⟨hvA, hwB⟩ | ⟨hvB, hwA⟩
  · exact h_dir hvw hvA hwB
  · exact (h_dir (G.adj_symm hvw) hwA hvB).symm
