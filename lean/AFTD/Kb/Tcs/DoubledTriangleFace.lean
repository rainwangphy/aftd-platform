import AFTD.Prelude

/-!
# DoubledTriangleFace

Topic: combinatorics   Node: f7c05473b449

Provenance: formalization of a published result. Source: arXiv:2611.12065, Section 2.3

A face of the doubled equilateral triangle triangulation T(n) of side n, which is either an up-triangle U(i,j) or a down-triangle D(i,j) on the front or back copy.
-/

/-- Faces of the doubled equilateral triangle triangulation T(n). -/
inductive DoubledTriangleFace (n : ℕ) : Type where
  | up (front : Bool) (i j : Fin n) (h : (i : ℕ) + j < n) : DoubledTriangleFace n
  | down (front : Bool) (i j : Fin n) (h : (i : ℕ) + j + 1 < n) : DoubledTriangleFace n
deriving DecidableEq, Fintype
