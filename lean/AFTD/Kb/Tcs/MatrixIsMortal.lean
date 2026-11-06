import AFTD.Prelude

/-!
# matrix_is_mortal

Topic: computability   Node: 8bcc4b649e74

Provenance: formalization of a published result. Source: arXiv:2611.06562 Section 1

A set of square matrices S is mortal if some non-empty finite product of matrices in S equals zero.
-/

/-- A set of square matrices S is mortal if there is a non-empty sequence of matrices in S whose product is zero. -/
def matrix_is_mortal {m : Type*} [Fintype m] [DecidableEq m] {α : Type*} [Semiring α] (S : Set (Matrix m m α)) : Prop := ∃ l : List (Matrix m m α), l ≠ [] ∧ (∀ M ∈ l, M ∈ S) ∧ l.prod = 0
