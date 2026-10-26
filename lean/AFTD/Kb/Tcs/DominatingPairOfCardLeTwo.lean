import AFTD.Prelude

/-!
# dominating_pair_of_card_le_two

Topic: graphs   Node: 17bae35ac954

Provenance: helper lemma. step towards p7_claw_free_dominating_pair_of_no_hole

In any graph with at most two vertices, the vertices themselves form a dominating set of size at most 2.
-/

/-- Any graph on at most 2 vertices has a dominating pair of vertices. -/
theorem dominating_pair_of_card_le_two {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Nonempty V] (h : Fintype.card V ≤ 2) :
    ∃ u v : V, ∀ w : V, w = u ∨ w = v ∨ G.Adj u w ∨ G.Adj v w := by
  classical
  by_cases h1 : Fintype.card V ≤ 1
  · obtain ⟨u⟩ := ‹Nonempty V›
    refine ⟨u, u, fun w => ?_⟩
    left
    exact Fintype.card_le_one_iff.mp h1 w u
  · have h2 : Fintype.card V = 2 := by omega
    have hc : (Finset.univ : Finset V).card = 2 := by
      rw [Finset.card_univ]; exact h2
    obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hc
    refine ⟨x, y, fun w => ?_⟩
    have hw : w ∈ (Finset.univ : Finset V) := Finset.mem_univ w
    rw [hset] at hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · left; rfl
    · right; left; rfl
