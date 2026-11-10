import AFTD.Prelude

/-!
# DoubledTriangleEdge

Topic: combinatorics   Node: cf3d3637be10

Provenance: formalization of a published result. Source: arXiv:2611.12065, Section 2.3

The inductive type DoubledTriangleEdge n of edges in the doubled equilateral triangle triangulation T(n), with six constructors: horiz_boundary (i : Fin n), horiz_interior (front : Bool) (i j : Fin n) (h : (i : ℕ) + j < n) (hj : 0 < (j : ℕ)), vert_boundary (j : Fin n), vert_interior (front : Bool) (i j : Fin n) (h : (i : ℕ) + j < n) (hi : 0 < (i : ℕ)), diag_boundary (i : Fin n), and diag_interior (front : Bool) (i j : Fin n) (h : (i : ℕ) + j + 1 < n), deriving DecidableEq and Fintype.
-/

/-- Edges of the doubled equilateral triangle triangulation T(n). -/
inductive DoubledTriangleEdge (n : ℕ) : Type where
  | horiz_boundary (i : Fin n) : DoubledTriangleEdge n
  | horiz_interior (front : Bool) (i : Fin n) (j : Fin n) (h : (i : ℕ) + j < n) (hj : 0 < (j : ℕ)) : DoubledTriangleEdge n
  | vert_boundary (j : Fin n) : DoubledTriangleEdge n
  | vert_interior (front : Bool) (i : Fin n) (j : Fin n) (h : (i : ℕ) + j < n) (hi : 0 < (i : ℕ)) : DoubledTriangleEdge n
  | diag_boundary (i : Fin n) : DoubledTriangleEdge n
  | diag_interior (front : Bool) (i : Fin n) (j : Fin n) (h : (i : ℕ) + j + 1 < n) : DoubledTriangleEdge n
deriving DecidableEq, Fintype
