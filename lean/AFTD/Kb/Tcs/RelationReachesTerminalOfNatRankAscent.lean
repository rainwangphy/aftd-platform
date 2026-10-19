import AFTD.Prelude

/-!
# relation_reaches_terminal_of_nat_rank_ascent

Topic: graphs   Node: 6e1b3b26b351

Provenance: helper lemma. step towards op223_poset_connectivity

Let P and Term be predicates and R a relation on a type α, with r : α → ℕ. If every non-terminal P-state X has a P-successor Y (that is, R X Y) with r Y < r X, then every P-state X starts a finite R-chain X → ⋯ → Q whose last element Q is terminal.
-/

/-- Ascent from a state to a terminal state through a ℕ-valued rank: a non-terminal P-state always has an R-successor of strictly smaller rank. -/
theorem relation_reaches_terminal_of_nat_rank_ascent {α : Type*} (P Term : α → Prop)
    (R : α → α → Prop) (r : α → ℕ)
    (h : ∀ X, P X → ¬ Term X → ∃ Y, P Y ∧ r Y < r X ∧ R X Y) :
    ∀ X, P X → ∃ Q, Term Q ∧ Relation.ReflTransGen R X Q := by
  suffices H : ∀ k, ∀ X, r X ≤ k → P X → ∃ Q, Term Q ∧ Relation.ReflTransGen R X Q by
    intro X hX
    exact H (r X) X le_rfl hX
  intro k
  induction k with
  | zero =>
    intro X hk hX
    by_cases hT : Term X
    · exact ⟨X, hT, Relation.ReflTransGen.refl⟩
    · obtain ⟨Y, -, hlt, -⟩ := h X hX hT
      omega
  | succ k ih =>
    intro X hk hX
    by_cases hT : Term X
    · exact ⟨X, hT, Relation.ReflTransGen.refl⟩
    · obtain ⟨Y, hPY, hlt, hR⟩ := h X hX hT
      obtain ⟨Q, hTQ, hstep⟩ := ih Y (by omega) hPY
      exact ⟨Q, hTQ, Relation.ReflTransGen.head hR hstep⟩
