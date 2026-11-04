import AFTD.Prelude

/-!
# has_strong_elimination

Topic: combinatorics   Node: 9e45bf2a15d2

Provenance: formalization of a published result. Source: arXiv:2611.01102, Definition 3.1

Given a type α with decidable equality, a finite collection C of finite subsets of α has the strong elimination property if for all C₁, C₂ ∈ C, every element x ∈ C₁ ∩ C₂, and every element y ∈ C₁ \ C₂, there exists some C₃ ∈ C such that y ∈ C₃ and C₃ ⊆ (C₁ ∪ C₂) \ {x}.
-/

/-- The strong elimination property for a collection of subsets: eliminating x while preserving y in C₁. -/
def has_strong_elimination {α : Type*} [DecidableEq α] (C : Finset (Finset α)) : Prop :=
  ∀ C₁ ∈ C, ∀ C₂ ∈ C, ∀ x ∈ C₁ ∩ C₂, ∀ y ∈ C₁ \ C₂,
    ∃ C₃ ∈ C, y ∈ C₃ ∧ C₃ ⊆ (C₁ ∪ C₂) \ {x}
