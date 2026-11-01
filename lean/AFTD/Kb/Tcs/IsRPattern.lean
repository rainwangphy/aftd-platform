import AFTD.Prelude

/-!
# is_R_pattern

Topic: combinatorics   Node: 32fd76bf76b2

Provenance: formalization of a published result. Source: arXiv:2610.37940 Section 6.3

A list of natural numbers β is an R-pattern if β is nonempty and every element of β is less than or equal to its last element.
-/

/-- An R-pattern is a nonempty list of natural numbers whose maximum entry is at the rightmost position. -/
def is_R_pattern (β : List ℕ) : Prop := ∃ h : β ≠ [], ∀ x ∈ β, x ≤ β.getLast h
