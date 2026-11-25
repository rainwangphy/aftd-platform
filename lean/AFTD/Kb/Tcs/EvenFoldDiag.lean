import AFTD.Prelude

/-!
# evenFoldDiag

Topic: combinatorics   Node: 02c1e9ff7345

Provenance: formalization of a published result. Source: arXiv:2611.28952, Section 1.1, (3)

The diagonal sequence of the even fold of a tridiagonal pair with parameter δ: for a diagonal list d, if d reverses to dn :: drest, it is the concatenation of drest.reverse, dn - δ, dn + δ, and drest (and empty if d is empty).
-/

/-- The diagonal sequence of the even fold of a tridiagonal pair: (d_1, ..., d_{n-1}, d_n - δ, d_n + δ, d_{n-1}, ..., d_1). -/
def evenFoldDiag {R : Type*} [Sub R] [Add R] (d : List R) (δ : R) : List R := match d.reverse with
  | [] => []
  | dn :: drest => drest.reverse ++ (dn - δ) :: (dn + δ) :: drest
