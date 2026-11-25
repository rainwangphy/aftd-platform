import AFTD.Prelude

/-!
# evenFoldOffDiag

Topic: combinatorics   Node: fae62caaa336

Provenance: formalization of a published result. Source: arXiv:2611.28952, Section 1.1, (3)

For any type R equipped with negation and one, and any list b : List R, evenFoldOffDiag b is the list obtained by concatenating b, the single element (-1 : R), and the reversal of b, that is b ++ (-1 : R) :: b.reverse.
-/

/-- The off-diagonal sequence of the even fold of a tridiagonal pair: b ++ (-1 : R) :: b.reverse. -/
def evenFoldOffDiag {R : Type*} [Neg R] [One R] (b : List R) : List R := b ++ (-1 : R) :: b.reverse
