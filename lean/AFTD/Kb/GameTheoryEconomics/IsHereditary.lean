import AFTD.Prelude

/-!
# is_hereditary

Topic: fair_division   Node: 3c28761cccf0

Provenance: formalization of a published result. Source: arXiv:2611.34488, Section 2

A set of finsets F is hereditary (or downward-closed) if the empty set belongs to F and every subset of an element of F also belongs to F.
-/

/-- A set of finsets is hereditary (downward-closed) if it contains ∅ and is closed under taking subsets. -/
def is_hereditary {α : Type*} (F : Set (Finset α)) : Prop := ∅ ∈ F ∧ ∀ {S T : Finset α}, S ∈ F → T ⊆ S → T ∈ F
