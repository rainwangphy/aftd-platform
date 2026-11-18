import AFTD.Prelude

/-!
# equal_cardinality_set_transition

Topic: combinatorics   Node: 42e6939764ac

Provenance: helper lemma. Elementary transition in the cyclic palette selection construction for OP-874.

For finite sets A and B of equal cardinality and any x in A, some y in B either equals x or lies outside A.
-/

theorem equal_cardinality_set_transition {Ω : Type*} [DecidableEq Ω]
    (A B : Finset Ω) (hcard : A.card = B.card) (x : Ω) (hx : x ∈ A) :
    ∃ y ∈ B, y = x ∨ y ∉ A := by
  by_cases hxB : x ∈ B
  · exact ⟨x, hxB, Or.inl rfl⟩
  · have hnot : ¬ B ⊆ A := by
      intro hBA
      have heq : B = A := Finset.eq_of_subset_of_card_le hBA (by omega)
      apply hxB
      rw [heq]
      exact hx
    obtain ⟨y, hyB, hyA⟩ := Finset.not_subset.mp hnot
    exact ⟨y, hyB, Or.inr hyA⟩
