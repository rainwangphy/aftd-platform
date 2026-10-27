import AFTD.Prelude

/-!
# OrderedTriple

Topic: combinatorics   Node: 66935d4c83aa

Provenance: formalization of a published result. Source: arXiv:2610.03808 Sec. 2.1

An ordered triple in a preordered type is a triple of elements (a, b, c) with a < b and b < c.
-/

/-- A strictly increasing triple of elements in a preordered type. -/
structure OrderedTriple (α : Type*) [Preorder α] where
  a : α
  b : α
  c : α
  ab : a < b
  bc : b < c
deriving DecidableEq
