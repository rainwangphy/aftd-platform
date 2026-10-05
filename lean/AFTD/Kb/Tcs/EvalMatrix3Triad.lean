import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad

/-!
# eval_matrix3_triad

Topic: algebraic_complexity   Node: 65d4d24e9e76

Given a commutative semiring R, a triad t of type Matrix3Triad R, and 3x3 matrices A and B over R, eval_matrix3_triad t A B is the scalar multiple of t.w by the product of the sum of t.u i j * A i j and the sum of t.v i j * B i j over all i and j in Fin 3.
-/

/-- Bilinear evaluation of a 3x3 triad on input matrices A and B. -/
def eval_matrix3_triad {R : Type*} [CommSemiring R] (t : Matrix3Triad R) (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  let sA := ∑ i : Fin 3, ∑ j : Fin 3, t.u i j * A i j
  let sB := ∑ i : Fin 3, ∑ j : Fin 3, t.v i j * B i j
  (sA * sB) • t.w
