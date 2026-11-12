import AFTD.Prelude

/-!
# chessboard

Topic: combinatorics   Node: 2df7cb11e090

Provenance: formalization of a published result. Source: arXiv:2611.12329 Piercing a Chessboard with Restricted Slopes, Section 1

For any natural number n, the chessboard of size n is the finite set of pairs of natural numbers (Finset (ℕ × ℕ)) given by the Cartesian product (Finset.range n) ×ˢ (Finset.range n).
-/

/-- The n x n chessboard of cells {0, ..., n-1} x {0, ..., n-1} as a Finset of pairs of natural numbers. -/
def chessboard (n : ℕ) : Finset (ℕ × ℕ) := (Finset.range n) ×ˢ (Finset.range n)
