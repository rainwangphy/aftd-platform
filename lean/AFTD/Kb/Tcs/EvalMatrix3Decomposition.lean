import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Triad

/-!
# eval_matrix3_decomposition

Topic: algebraic_complexity   Node: eb241ba07924

Given a commutative semiring R, a list L of Matrix3Triad R, and 3x3 matrices A and B over R, eval_matrix3_decomposition L A B is the sum of eval_matrix3_triad t A B for t in L.
-/

/-- Evaluation of a list of 3x3 triads on input matrices A and B. -/
def eval_matrix3_decomposition {R : Type*} [CommSemiring R] (L : List (Matrix3Triad R)) (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  (L.map (fun t => eval_matrix3_triad t A B)).sum
