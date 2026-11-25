import AFTD.Prelude

/-!
# tridiagonalCharpoly

Topic: combinatorics   Node: 46e41dc9ac3a

Provenance: formalization of a published result. Source: arXiv:2611.28952, Section 2.1, (8)

For any commutative ring R, tridiagonalCharpoly is the noncomputable function taking two curried list arguments d, b : List R and returning Polynomial R, defined by structural recursion on d: if d = [] then 1; if d = [d0] then Polynomial.X - Polynomial.C d0; if d = d0 :: d1 :: ds and b = [] then (Polynomial.X - Polynomial.C d0) * tridiagonalCharpoly (d1 :: ds) []; and if d = d0 :: d1 :: ds and b = b0 :: bs then (Polynomial.X - Polynomial.C d0) * tridiagonalCharpoly (d1 :: ds) bs - Polynomial.C b0 * tridiagonalCharpoly ds bs.tail.
-/

/-- Characteristic polynomial of a tridiagonal pair (d, b) defined by the three-term recurrence. -/
noncomputable def tridiagonalCharpoly {R : Type*} [CommRing R] : List R → List R → Polynomial R
  | [], _ => 1
  | [d0], _ => Polynomial.X - Polynomial.C d0
  | d0 :: d1 :: ds, [] => (Polynomial.X - Polynomial.C d0) * tridiagonalCharpoly (d1 :: ds) []
  | d0 :: d1 :: ds, b0 :: bs =>
    (Polynomial.X - Polynomial.C d0) * tridiagonalCharpoly (d1 :: ds) bs -
      Polynomial.C b0 * tridiagonalCharpoly ds bs.tail
