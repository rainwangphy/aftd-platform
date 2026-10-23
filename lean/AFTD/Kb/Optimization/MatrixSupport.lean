import AFTD.Prelude

/-!
# matrix_support

Topic: integer_programming   Node: ecc131190313

Provenance: formalization of a published result. Source: scout/2610-04498-rank-sensitive-vertex-bounds-for-semidefinite-lifts.md:2050

The support of an m × n matrix M is the set of index pairs (i, j) ∈ m × n such that M_ij ≠ 0.
-/

/-- The support of a matrix is the set of entry index pairs where it is nonzero. -/
def matrix_support {m n α : Type*} [Zero α] (M : Matrix m n α) : Set (m × n) := {p : m × n | M p.1 p.2 ≠ 0}
