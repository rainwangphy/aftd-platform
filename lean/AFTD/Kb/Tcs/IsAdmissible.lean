import AFTD.Prelude

/-!
# IsAdmissible

Topic: combinatorics   Node: 0b810cea9b44

Provenance: formalization of a published result. Source: arXiv:2610.34372, Definition 1.1

A finite set A of positive integers is admissible if for any two subsets B and C of A, if the sum of elements in B equals the sum of elements in C, then B and C have the same cardinality.
-/

/-- A finite set of positive integers is admissible if any two subsets with the same sum have the same cardinality. -/
def IsAdmissible (A : Finset ℕ) : Prop := ∀ B C, B ⊆ A → C ⊆ A → B.sum id = C.sum id → B.card = C.card
