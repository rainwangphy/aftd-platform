import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.EvalMatrix3DecompositionApply
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition

/-!
# matrix3_tensor_rank_le_23_of_comm_ring

Topic: algebraic_complexity   Node: b2e30785d32d

Provenance: formalization of a published result. Source: A noncommutative algorithm for multiplying matrices using 23 multiplications (1976), as cited in Lower Bound of 22 for 3x3 Matrix Multiplication over the Integers, arXiv:2610.01639, Sec. 1 and Sec. 7 (upper bound 23); the integer coefficients 0, 1, -1 make it valid over every commutative ring

Over every commutative ring R, 3x3 matrix multiplication has a valid bilinear decomposition with 23 products (the classical 23-multiplication algorithm with integer coefficients 0, 1, -1); hence its rank over R is at most 23.
-/

/-- An explicit list of 23 triads over any commutative ring; its 23 products compute the 3×3 matrix product. -/
def matrix3_triads_23 (R : Type*) [CommRing R] : List (Matrix3Triad R) :=
  [
    ⟨!![1, 1, 1; -1, -1, 0; 0, -1, -1], !![0, 0, 0; 0, 1, 0; 0, 0, 0], !![0, 1, 0; 0, 0, 0; 0, 0, 0]⟩,
    ⟨!![1, 0, 0; -1, 0, 0; 0, 0, 0], !![0, -1, 0; 0, 1, 0; 0, 0, 0], !![0, 0, 0; 1, 1, 0; 0, 0, 0]⟩,
    ⟨!![0, 0, 0; 0, 1, 0; 0, 0, 0], !![-1, 1, 0; 1, -1, -1; -1, 0, 1], !![0, 0, 0; 1, 0, 0; 0, 0, 0]⟩,
    ⟨!![-1, 0, 0; 1, 1, 0; 0, 0, 0], !![1, -1, 0; 0, 1, 0; 0, 0, 0], !![0, 1, 0; 1, 1, 0; 0, 0, 0]⟩,
    ⟨!![0, 0, 0; 1, 1, 0; 0, 0, 0], !![-1, 1, 0; 0, 0, 0; 0, 0, 0], !![0, 1, 0; 0, 1, 0; 0, 0, 0]⟩,
    ⟨!![1, 0, 0; 0, 0, 0; 0, 0, 0], !![1, 0, 0; 0, 0, 0; 0, 0, 0], !![1, 1, 1; 1, 1, 0; 1, 0, 1]⟩,
    ⟨!![-1, 0, 0; 0, 0, 0; 1, 1, 0], !![1, 0, -1; 0, 0, 1; 0, 0, 0], !![0, 0, 1; 0, 0, 0; 1, 0, 1]⟩,
    ⟨!![-1, 0, 0; 0, 0, 0; 1, 0, 0], !![0, 0, 1; 0, 0, -1; 0, 0, 0], !![0, 0, 0; 0, 0, 0; 1, 0, 1]⟩,
    ⟨!![0, 0, 0; 0, 0, 0; 1, 1, 0], !![-1, 0, 1; 0, 0, 0; 0, 0, 0], !![0, 0, 1; 0, 0, 0; 0, 0, 1]⟩,
    ⟨!![1, 1, 1; 0, -1, -1; -1, -1, 0], !![0, 0, 0; 0, 0, 1; 0, 0, 0], !![0, 0, 1; 0, 0, 0; 0, 0, 0]⟩,
    ⟨!![0, 0, 0; 0, 0, 0; 0, 1, 0], !![-1, 0, 1; 1, -1, -1; -1, 1, 0], !![0, 0, 0; 0, 0, 0; 1, 0, 0]⟩,
    ⟨!![0, 0, -1; 0, 0, 0; 0, 1, 1], !![0, 0, 0; 0, 1, 0; 1, -1, 0], !![0, 1, 0; 0, 0, 0; 1, 1, 0]⟩,
    ⟨!![0, 0, 1; 0, 0, 0; 0, 0, -1], !![0, 0, 0; 0, 1, 0; 0, -1, 0], !![0, 0, 0; 0, 0, 0; 1, 1, 0]⟩,
    ⟨!![0, 0, 1; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 0, 0, 0; 1, 0, 0], !![1, 1, 1; 1, 0, 1; 1, 1, 0]⟩,
    ⟨!![0, 0, 0; 0, 0, 0; 0, 1, 1], !![0, 0, 0; 0, 0, 0; -1, 1, 0], !![0, 1, 0; 0, 0, 0; 0, 1, 0]⟩,
    ⟨!![0, 0, -1; 0, 1, 1; 0, 0, 0], !![0, 0, 0; 0, 0, 1; 1, 0, -1], !![0, 0, 1; 1, 0, 1; 0, 0, 0]⟩,
    ⟨!![0, 0, 1; 0, 0, -1; 0, 0, 0], !![0, 0, 0; 0, 0, 1; 0, 0, -1], !![0, 0, 0; 1, 0, 1; 0, 0, 0]⟩,
    ⟨!![0, 0, 0; 0, 1, 1; 0, 0, 0], !![0, 0, 0; 0, 0, 0; -1, 0, 1], !![0, 0, 1; 0, 0, 1; 0, 0, 0]⟩,
    ⟨!![0, 1, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 1, 0, 0; 0, 0, 0], !![1, 0, 0; 0, 0, 0; 0, 0, 0]⟩,
    ⟨!![0, 0, 0; 0, 0, 1; 0, 0, 0], !![0, 0, 0; 0, 0, 0; 0, 1, 0], !![0, 0, 0; 0, 1, 0; 0, 0, 0]⟩,
    ⟨!![0, 0, 0; 1, 0, 0; 0, 0, 0], !![0, 0, 1; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 0, 0, 1; 0, 0, 0]⟩,
    ⟨!![0, 0, 0; 0, 0, 0; 1, 0, 0], !![0, 1, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 0, 0, 0; 0, 1, 0]⟩,
    ⟨!![0, 0, 0; 0, 0, 0; 0, 0, 1], !![0, 0, 0; 0, 0, 0; 0, 0, 1], !![0, 0, 0; 0, 0, 0; 0, 0, 1]⟩
  ]

theorem matrix3_triads_23_length (R : Type*) [CommRing R] : (matrix3_triads_23 R).length = 23 := rfl

theorem matrix3_triads_23_valid (R : Type*) [CommRing R] :
    is_valid_matrix3_decomposition (matrix3_triads_23 R) := by
  set_option maxHeartbeats 1000000 in
  intro A B
  ext i j
  rw [eval_matrix3_decomposition_apply]
  fin_cases i <;> fin_cases j <;>
    simp [matrix3_triads_23, Fin.sum_univ_three, Matrix.mul_apply] <;> ring

theorem matrix3_tensor_rank_le_23_of_comm_ring (R : Type*) [CommRing R] : matrix3_tensor_rank_le R 23 := ⟨matrix3_triads_23 R, le_of_eq (matrix3_triads_23_length R), matrix3_triads_23_valid R⟩
