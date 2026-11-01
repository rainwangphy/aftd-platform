import AFTD.Prelude

/-!
# is_M_pattern

Topic: combinatorics   Node: 27e529d1029f

Provenance: formalization of a published result. Source: arXiv:2610.37940 Section 6.3

A list of natural numbers β is an M-pattern if β is nonempty, some element of β is strictly greater than its head, and some element of β is strictly greater than its last element.
-/

/-- An M-pattern is a nonempty list of natural numbers whose maximum entry is at an interior position. -/
def is_M_pattern (β : List ℕ) : Prop := ∃ h : β ≠ [], (∃ x ∈ β, β.head h < x) ∧ (∃ x ∈ β, β.getLast h < x)
