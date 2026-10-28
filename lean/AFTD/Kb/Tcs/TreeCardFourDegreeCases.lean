import AFTD.Prelude

/-!
# tree_card_four_degree_cases

Topic: graphs   Node: 9886ba1de405

Provenance: helper lemma. step towards caterpillar_third_t_chromatic_specialization_fiber_le_two

Every tree on 4 vertices either has a vertex of degree 3 or all its vertices have degree at most 2.
-/

/-- Every tree on 4 vertices either has a vertex of degree 3 (a star) or has all degrees at most 2 (a path). -/
theorem tree_card_four_degree_cases {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (hcard : Fintype.card V = 4) :
    (∃ v : V, T.degree v = 3) ∨ (∀ v : V, T.degree v ≤ 2) := by
  have _ := hT
  by_cases h : ∃ v : V, T.degree v = 3
  · exact Or.inl h
  · right
    intro v
    have hlt := T.degree_lt_card_verts v
    rw [hcard] at hlt
    have hne : T.degree v ≠ 3 := fun heq => h ⟨v, heq⟩
    omega
