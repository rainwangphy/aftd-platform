import AFTD.Prelude

/-!
# collection_min_nonempty

Topic: combinatorics   Node: e6c99289152f

Provenance: formalization of a published result. Source: arXiv:2611.01102, Definition 2.4

Given a type α with decidable equality and a finite collection C of finite subsets of α, collection_min_nonempty C is the subcollection of all sets S ∈ C such that S is nonempty, and for every T ∈ C, if T is nonempty and T ⊆ S, then T = S.
-/

/-- The minimal nonempty sets in a collection C of finite sets: nonempty sets with no proper nonempty subset in C. -/
def collection_min_nonempty {α : Type*} [DecidableEq α] (C : Finset (Finset α)) : Finset (Finset α) :=
  C.filter fun S => S.Nonempty ∧ ∀ T ∈ C, T.Nonempty → T ⊆ S → T = S
