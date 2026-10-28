import AFTD.Prelude

/-!
# is_two_type_allocation

Topic: fair_division   Node: 4ab701076fce

Provenance: formalization of a published result. Source: arXiv:2610.19099

An allocation of a goods of type A and b goods of type B among n agents is a pair of non-negative integer count vectors (x, y) summing to a and b respectively.
-/

/-- Complete count allocation of two types of goods with counts a and b among n agents. -/
def is_two_type_allocation (n a b : ℕ) (x y : Fin n → ℕ) : Prop := (∑ i, x i = a) ∧ (∑ i, y i = b)
