import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Decomposition

/-!
# is_valid_matrix3_decomposition

Topic: algebraic_complexity   Node: ee3b00eaefcb

Given a commutative semiring R and a list L of Matrix3Triad R, is_valid_matrix3_decomposition L asserts that for all 3x3 matrices A and B over R, eval_matrix3_decomposition L A B equals A * B.
-/

/-- A triad decomposition is valid for 3x3 matrix multiplication if it computes A * B for all A and B. -/
def is_valid_matrix3_decomposition {R : Type*} [CommSemiring R] (L : List (Matrix3Triad R)) : Prop :=
  ∀ A B : Matrix (Fin 3) (Fin 3) R, eval_matrix3_decomposition L A B = A * B
