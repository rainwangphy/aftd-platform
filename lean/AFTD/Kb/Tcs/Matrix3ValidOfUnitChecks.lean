import AFTD.Prelude
import AFTD.Kb.Tcs.EvalMatrix3TriadSmulLeft
import AFTD.Kb.Tcs.EvalMatrix3TriadSmulRight
import AFTD.Kb.Tcs.EvalMatrix3DecompositionSumLeft
import AFTD.Kb.Tcs.EvalMatrix3DecompositionSumRight
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Decomposition

/-!
# matrix3_valid_of_unit_checks

Topic: algebraic_complexity   Node: c7aaa52d3442

Provenance: helper lemma. step towards matrix3_tensor_rank_zmod2_le_22

If a list L of triads over a commutative semiring R evaluates to matrix multiplication on all 81 pairs of matrix units, then L is a valid decomposition: eval L A B = A * B for all 3x3 matrices A, B over R.
-/

lemma matrix3_valid_of_unit_checks_cons {R : Type*} [CommSemiring R]
    (t : Matrix3Triad R) (L : List (Matrix3Triad R)) (A B : Matrix (Fin 3) (Fin 3) R) :
    eval_matrix3_decomposition (t :: L) A B = eval_matrix3_triad t A B + eval_matrix3_decomposition L A B := rfl

lemma matrix3_valid_of_unit_checks_smul_left {R : Type*} [CommSemiring R]
    (L : List (Matrix3Triad R)) (c : R) (A B : Matrix (Fin 3) (Fin 3) R) :
    eval_matrix3_decomposition L (c • A) B = c • eval_matrix3_decomposition L A B := by
  induction L with
  | nil => simp [eval_matrix3_decomposition]
  | cons t L' ih =>
    rw [matrix3_valid_of_unit_checks_cons, matrix3_valid_of_unit_checks_cons,
        eval_matrix3_triad_smul_left, ih, smul_add]

lemma matrix3_valid_of_unit_checks_smul_right {R : Type*} [CommSemiring R]
    (L : List (Matrix3Triad R)) (c : R) (A B : Matrix (Fin 3) (Fin 3) R) :
    eval_matrix3_decomposition L A (c • B) = c • eval_matrix3_decomposition L A B := by
  induction L with
  | nil => simp [eval_matrix3_decomposition]
  | cons t L' ih =>
    rw [matrix3_valid_of_unit_checks_cons, matrix3_valid_of_unit_checks_cons,
        eval_matrix3_triad_smul_right, ih, smul_add]

lemma matrix3_valid_of_unit_checks_single_eq_smul {R : Type*} [CommSemiring R] (i j : Fin 3) (c : R) :
    Matrix.single i j c = c • Matrix.single i j (1 : R) := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

lemma matrix3_valid_of_unit_checks_eq_sum_smul_single {R : Type*} [CommSemiring R] (A : Matrix (Fin 3) (Fin 3) R) :
    A = ∑ i : Fin 3, ∑ j : Fin 3, A i j • Matrix.single i j (1 : R) := by
  nth_rw 1 [Matrix.matrix_eq_sum_single A]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  exact matrix3_valid_of_unit_checks_single_eq_smul i j (A i j)

/-- Agreement with matrix multiplication on the 81 matrix-unit pairs extends to all pairs of matrices, because both sides are bilinear and every matrix is a sum of matrix units. -/
theorem matrix3_valid_of_unit_checks {R : Type*} [CommSemiring R] (L : List (Matrix3Triad R))
    (h : ∀ i j k l : Fin 3,
      eval_matrix3_decomposition L (Matrix.single i j (1 : R)) (Matrix.single k l (1 : R))
        = Matrix.single i j (1 : R) * Matrix.single k l (1 : R)) :
    is_valid_matrix3_decomposition L := by
  intro A B
  nth_rw 1 [matrix3_valid_of_unit_checks_eq_sum_smul_single A]
  nth_rw 1 [matrix3_valid_of_unit_checks_eq_sum_smul_single B]
  simp_rw [eval_matrix3_decomposition_sum_left, eval_matrix3_decomposition_sum_right,
           matrix3_valid_of_unit_checks_smul_left, matrix3_valid_of_unit_checks_smul_right]
  simp_rw [h]
  nth_rw 2 [matrix3_valid_of_unit_checks_eq_sum_smul_single A]
  nth_rw 2 [matrix3_valid_of_unit_checks_eq_sum_smul_single B]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
