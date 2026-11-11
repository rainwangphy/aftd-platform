import AFTD.Prelude

/-!
# DoubledTriangleRing

Topic: combinatorics   Node: 025e81407ee0

Provenance: formalization of a published result. Source: arXiv:2611.12065, Definition 4.1

A ring of the doubled equilateral triangle triangulation T(n), which is either an x-ring X_k, a y-ring Y_k, or a z-ring Z_k for an index k < n.
-/

/-- A ring of T(n), parameterized by coordinate family (x, y, or z) and strip index k : Fin n. -/
inductive DoubledTriangleRing (n : ℕ) : Type where
  | x (k : Fin n) : DoubledTriangleRing n
  | y (k : Fin n) : DoubledTriangleRing n
  | z (k : Fin n) : DoubledTriangleRing n
deriving DecidableEq, Fintype
