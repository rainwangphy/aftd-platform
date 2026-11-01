import AFTD.Prelude

/-!
# is_L_pattern

Topic: combinatorics   Node: f20ae58ad726

Provenance: formalization of a published result. Source: arXiv:2610.37940 Section 6.3

A list of natural numbers β is an L-pattern if β is nonempty and every element of β is less than or equal to its head.
-/

/-- An L-pattern is a nonempty list of natural numbers whose maximum entry is at the leftmost position. -/
def is_L_pattern (β : List ℕ) : Prop := ∃ h : β ≠ [], ∀ x ∈ β, x ≤ β.head h
