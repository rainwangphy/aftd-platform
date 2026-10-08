import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixDetEqPermanentOfCharTwo

/-!
# matrix_permanent_mul_of_char_two

Topic: algebraic_complexity   Node: b57ba718e1c3

Provenance: original. Related work: folklore; Valiant 1979

For every commutative ring R of characteristic 2 and any square matrices A and B over R indexed by a finite type n with decidable equality, the permanent of the matrix product A * B equals the product of the permanent of A and the permanent of B.
-/

/-- Over any commutative ring of characteristic 2, the permanent of a product of square matrices equals the product of their permanents. -/
theorem matrix_permanent_mul_of_char_two {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R] [CharP R 2] (A B : Matrix n n R) : (A * B).permanent = A.permanent * B.permanent := by
  rw [← matrix_det_eq_permanent_of_char_two, ← matrix_det_eq_permanent_of_char_two A, ← matrix_det_eq_permanent_of_char_two B]
  exact Matrix.det_mul A B
