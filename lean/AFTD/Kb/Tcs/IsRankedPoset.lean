import AFTD.Prelude

/-!
# is_ranked_poset

Topic: combinatorics   Node: 7a5cb4e74ebd

Provenance: formalization of a published result. Source: arXiv:2610.24148, Section 2.3

A function rank : α → ℤ from a partially ordered type α to the integers ℤ is a ranked poset structure if it is monotone (for all a b : α, a ≤ b implies rank a ≤ rank b), increases by 2 along every cover relation (for all a b : α, a ⋖ b implies rank b = rank a + 2), and assigns integers of the same parity modulo 2 to all elements (for all a b : α, rank a ≡ rank b [ZMOD 2]).
-/

/-- A ranked poset with integer rank stepping by 2 and uniform parity. -/
def is_ranked_poset {α : Type*} [PartialOrder α] (rank : α → ℤ) : Prop :=
  (∀ {a b : α}, a ≤ b → rank a ≤ rank b) ∧
  (∀ {a b : α}, a ⋖ b → rank b = rank a + 2) ∧
  (∀ a b : α, rank a ≡ rank b [ZMOD 2])
