import AFTD.Prelude

/-!
# finset_is_midpoint_balanced

Topic: combinatorics   Node: 00b698734eed

Provenance: formalization of a published result. Source: arXiv:2610.09349 (A near-quadratic lower bound for sets with no unique sums), Definition A.1 (balanced set).

A finite set B is balanced: it is nonempty and every b ∈ B satisfies 2b = u + v for two distinct elements u, v of B other than b.
-/

/-- `B` is balanced: nonempty, and every `b ∈ B` is the midpoint `2b = u + v` of two distinct elements `u, v ∈ B \ {b}`. -/
def finset_is_midpoint_balanced {G : Type*} [AddCommMonoid G] (B : Finset G) : Prop :=
  B.Nonempty ∧ ∀ b ∈ B, ∃ u ∈ B, ∃ v ∈ B, u ≠ b ∧ v ≠ b ∧ u ≠ v ∧ b + b = u + v
