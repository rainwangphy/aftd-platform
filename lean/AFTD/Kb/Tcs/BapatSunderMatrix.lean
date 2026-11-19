import AFTD.Prelude

/-!
# bapat_sunder_matrix

Topic: combinatorics   Node: 6ffc07c5d041

Provenance: formalization of a published result. Source: arXiv:2611.23269, Eq. (2)

For any commutative semiring R, any natural number n, and any square matrix A of size (n+1) x (n+1) over R, the Bapat-Sunder matrix of A is the (n+1) x (n+1) matrix whose (i,j) entry is A i j times the permanent of the submatrix obtained by deleting row i and column j.
-/

/-- The Bapat-Sunder matrix of a square matrix A of size n + 1. -/
def bapat_sunder_matrix {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j => A i j * (A.submatrix i.succAbove j.succAbove).permanent
