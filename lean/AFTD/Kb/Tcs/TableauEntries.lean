import AFTD.Prelude

/-!
# tableau_entries

Topic: combinatorics   Node: b0bcfeb66cf3

Provenance: formalization of a published result. Source: arXiv:2611.07715, Section 4

For an abstract finite type α : Type* with [Fintype α] and a filling M : α → ℕ assigning natural numbers to elements of α, tableau_entries M is the multiset of natural numbers obtained by mapping M over Finset.univ of α.
-/

/-- The multiset of entries in a finite tableau filling. -/
def tableau_entries {α : Type*} [Fintype α] (M : α → ℕ) : Multiset ℕ := Finset.univ.val.map M
