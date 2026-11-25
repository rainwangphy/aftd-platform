import AFTD.Prelude

/-!
# oddFoldDiag

Topic: combinatorics   Node: a808bf82bfa8

Provenance: formalization of a published result. Source: arXiv:2611.28952, Section 1.1, (2)

The diagonal sequence of the odd fold of a tridiagonal pair: for a diagonal list d, it is the list obtained by concatenating d, 0, and the reversal of d.
-/

/-- The diagonal sequence of the odd fold of a tridiagonal pair: (d, 0, rev d). -/
def oddFoldDiag {R : Type*} [Zero R] (d : List R) : List R := d ++ 0 :: d.reverse
