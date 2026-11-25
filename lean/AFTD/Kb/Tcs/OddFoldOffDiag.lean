import AFTD.Prelude

/-!
# oddFoldOffDiag

Topic: combinatorics   Node: a384bc8bca53

Provenance: formalization of a published result. Source: arXiv:2611.28952, Section 1.1, (2)

The off-diagonal sequence of the odd fold of a tridiagonal pair with parameter ε: for an off-diagonal list b, it is the list obtained by concatenating b, ε, -ε, and the reversal of b.
-/

/-- The off-diagonal sequence of the odd fold of a tridiagonal pair: (b, ε, -ε, rev b). -/
def oddFoldOffDiag {R : Type*} [Neg R] (b : List R) (ε : R) : List R := b ++ ε :: -ε :: b.reverse
