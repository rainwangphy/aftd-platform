import AFTD.Prelude

/-!
# Order

Topic: combinatorics   Node: 1c90330ddb88

Provenance: formalization of a published result. Source: arXiv:2610.39311 Definition 1

An order of dimension d is a permutation of the attribute set {0, ..., d-1}, represented as a list without duplicates containing all elements.
-/

/-- An order of dimension d is a permutation of Fin d, represented as a list of length d without duplicates. -/
structure Order (d : ℕ) where
  elems : List (Fin d)
  nodup : elems.Nodup
  length_eq : elems.length = d
deriving DecidableEq
