import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixNuclearNorm
import AFTD.Kb.Tcs.SingularValuesNonneg
import AFTD.Kb.Tcs.SingularValues

/-!
# matrix_nuclear_norm_nonneg

Topic: information   Node: 3fa8b8e34c24

Provenance: helper lemma. folklore

For any square real matrix $M$, its nuclear norm is non-negative.
-/

/-- The nuclear norm of any square real matrix is non-negative. -/
theorem matrix_nuclear_norm_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) :
    0 ≤ matrix_nuclear_norm M := by
  unfold matrix_nuclear_norm
  exact Finset.sum_nonneg fun i _ => singularValues_nonneg _ i
