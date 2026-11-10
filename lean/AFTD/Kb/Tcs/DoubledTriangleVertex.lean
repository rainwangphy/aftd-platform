import AFTD.Prelude

/-!
# DoubledTriangleVertex

Topic: combinatorics   Node: b31c5027fb43

Provenance: formalization of a published result. Source: arXiv:2611.12065, Section 2.3

A vertex of the doubled equilateral triangle triangulation T(n), classified as either a boundary vertex or an interior vertex on the front or back.
-/

/-- Vertices of the doubled equilateral triangle triangulation T(n). -/
inductive DoubledTriangleVertex (n : ℕ) : Type where
  | boundary (i j : Fin (n + 1)) (h_le : (i : ℕ) + j ≤ n)
      (h_bd : (i : ℕ) = 0 ∨ (j : ℕ) = 0 ∨ (i : ℕ) + j = n) : DoubledTriangleVertex n
  | interior (front : Bool) (i j : Fin (n + 1))
      (hi : 0 < (i : ℕ)) (hj : 0 < (j : ℕ)) (h_lt : (i : ℕ) + j < n) : DoubledTriangleVertex n
deriving DecidableEq, Fintype
