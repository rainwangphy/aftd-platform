import AFTD.Prelude

/-!
# is_bh

Topic: combinatorics   Node: f190416defd8

Provenance: formalization of a published result. Source: scout/2611-01871-infinite-generalized-sidon-sets-with-a-negative-answer-to-a.md:90

A set A of natural numbers is a B_h set if every sum of h elements from A (with repetitions allowed) uniquely determines the multiset of summands.
-/

/-- A set A of natural numbers is a B_h set if every sum of h elements from A uniquely determines the multiset of summands. -/
def is_bh (h : ℕ) (A : Set ℕ) : Prop := ∀ (s t : Multiset ℕ), (∀ x ∈ s, x ∈ A) → (∀ x ∈ t, x ∈ A) →
    s.card = h → t.card = h → s.sum = t.sum → s = t
