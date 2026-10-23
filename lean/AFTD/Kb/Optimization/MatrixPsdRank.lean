import AFTD.Prelude
import AFTD.Kb.Optimization.MatrixHasPsdFactorization

/-!
# matrix_psd_rank

Topic: integer_programming   Node: be60ff0dca70

Provenance: formalization of a published result. Source: scout/2610-04498-rank-sensitive-vertex-bounds-for-semidefinite-lifts.md:351

For types m and n, the positive semidefinite rank (psd rank) of a real matrix M : Matrix m n ℝ is the infimum of the set of natural numbers r such that M has a positive semidefinite factorization of size r.
-/

/-- The positive semidefinite rank of a real matrix is the minimum size of a positive semidefinite factorization. -/
noncomputable def matrix_psd_rank {m n : Type*} (M : Matrix m n ℝ) : ℕ := sInf {r : ℕ | matrix_has_psd_factorization M r}
