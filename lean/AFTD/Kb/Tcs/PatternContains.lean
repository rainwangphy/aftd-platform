import AFTD.Prelude

/-!
# pattern_contains

Topic: combinatorics   Node: 3d9d0879eb28

Provenance: formalization of a published result. Source: arXiv:2610.37940 Section 2

A list of natural numbers π pattern-contains a list of natural numbers τ if some sublist s of π has the same length as τ and satisfies s[i] < s[j] ↔ τ[i] < τ[j] for all indices i, j.
-/

/-- Pattern containment on lists of natural numbers. -/
def pattern_contains (π τ : List ℕ) : Prop := ∃ s : List ℕ, s.Sublist π ∧ ∃ h : s.length = τ.length,
    ∀ (i j : Fin s.length), s[i] < s[j] ↔ τ[i.cast h] < τ[j.cast h]
