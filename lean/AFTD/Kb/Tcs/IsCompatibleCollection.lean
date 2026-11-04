import AFTD.Prelude

/-!
# is_compatible_collection

Topic: graphs   Node: 771f90c88476

Provenance: formalization of a published result. Source: arXiv:2611.01102 Sec. 2, Definition 2.6 and line 201

For an arbitrary type V with decidable equality, a finite collection C of finite subsets of V (C : Finset (Finset V)) is compatible if for all distinct sets C1, C2 in C and every element x in C1 ∩ C2, there exists a set C3 in C such that C3 ⊆ (C1 ∪ C2) \ {x}.
-/

/-- A collection of subsets is compatible if for distinct C1, C2 and x in C1 ∩ C2, there is C3 ⊆ (C1 ∪ C2) \ {x}. -/
def is_compatible_collection {V : Type*} [DecidableEq V] (C : Finset (Finset V)) : Prop := ∀ C1 ∈ C, ∀ C2 ∈ C, C1 ≠ C2 → ∀ x ∈ C1 ∩ C2, ∃ C3 ∈ C, C3 ⊆ (C1 ∪ C2) \ {x}
