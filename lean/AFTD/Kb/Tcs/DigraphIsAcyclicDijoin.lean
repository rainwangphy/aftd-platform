import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.DigraphDijoin

/-!
# digraph_is_acyclic_dijoin

Topic: graphs   Node: 5b4b6341cfc6

Provenance: helper lemma. Helper for the upper bound inv(D₁ → D₂) ≤ inv(D₁) + inv(D₂) of arXiv:2610.13798, Sec. 1.

The dijoin of two acyclic digraphs is acyclic: a directed walk never comes back from the D₂ side to the D₁ side.
-/

theorem digraph_is_acyclic_dijoin {V W : Type*} (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_acyclic D₁) (h₂ : digraph_is_acyclic D₂) :
    digraph_is_acyclic (digraph_dijoin D₁ D₂) := by
  have key : ∀ x y, Relation.TransGen (digraph_dijoin D₁ D₂).Adj x y →
      (∀ a b, x = .inl a → y = .inl b → Relation.TransGen D₁.Adj a b) ∧
      (∀ a b, x = .inr a → y = .inr b → Relation.TransGen D₂.Adj a b) ∧
      (∀ a b, x = .inr a → y = .inl b → False) := by
    intro x y h
    induction h with
    | single hxy =>
      refine ⟨?_, ?_, ?_⟩ <;> rintro a b rfl rfl
      · exact .single hxy
      · exact .single hxy
      · exact hxy
    | @tail b c _ hbc ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih
      refine ⟨?_, ?_, ?_⟩ <;> rintro a c' rfl rfl
      · rcases b with b | b
        · exact .tail (ih1 a b rfl rfl) hbc
        · exact hbc.elim
      · rcases b with b | b
        · exact (ih3 a b rfl rfl).elim
        · exact .tail (ih2 a b rfl rfl) hbc
      · rcases b with b | b
        · exact ih3 a b rfl rfl
        · exact hbc
  intro x hx
  rcases x with a | a
  · exact h₁ a ((key _ _ hx).1 a a rfl rfl)
  · exact h₂ a ((key _ _ hx).2.1 a a rfl rfl)
