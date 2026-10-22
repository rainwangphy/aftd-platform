import AFTD.Prelude

/-!
# has_constant_level_card

Topic: combinatorics   Node: 8a6e74eadb4b

Provenance: formalization of a published result. Source: arXiv:2610.24148, Section 4.1

A function f : α → ℤ on a finite type with decidable equality has constant level cardinality if any two non-empty fibers have the same cardinality: for all integers j and k, if the fiber of j is non-empty and the fiber of k is non-empty, then their cardinalities are equal.
-/

/-- A function has constant level cardinality if all non-empty fibers have equal size. -/
def has_constant_level_card {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℤ) : Prop :=
  ∀ j k : ℤ,
    (Finset.univ.filter (fun x : α => f x = j)).Nonempty →
    (Finset.univ.filter (fun x : α => f x = k)).Nonempty →
    (Finset.univ.filter (fun x : α => f x = j)).card =
    (Finset.univ.filter (fun x : α => f x = k)).card
