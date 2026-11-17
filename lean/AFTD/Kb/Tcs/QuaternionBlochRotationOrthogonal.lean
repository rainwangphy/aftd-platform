import AFTD.Prelude
import AFTD.Kb.Tcs.QuaternionBlochRotation

/-!
# quaternion_bloch_rotation_orthogonal

Topic: quantum   Node: f934d926fd44

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, quaternion-to-rotation parametrization.

For unit quaternion coordinates, the associated real matrix is orthogonal and has determinant one.
-/

theorem quaternion_bloch_rotation_orthogonal (q : Fin 4 → ℝ)
    (hq : (∑ i, (q i)^2) = 1) :
    (quaternion_bloch_rotation q).transpose * quaternion_bloch_rotation q = 1 ∧
      (quaternion_bloch_rotation q).det = 1 := by
  have hm : (quaternion_bloch_rotation q).transpose * quaternion_bloch_rotation q =
      (∑ i, (q i)^2)^2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quaternion_bloch_rotation, Matrix.mul_apply, Fin.sum_univ_three,
        Fin.sum_univ_four, Matrix.cons_val_two] <;> ring
  have hd : (quaternion_bloch_rotation q).det = (∑ i, (q i)^2)^3 := by
    simp [quaternion_bloch_rotation, Matrix.det_fin_three, Fin.sum_univ_four,
      Matrix.cons_val_two]
    ring
  constructor
  · rw [hm, hq]
    simp
  · rw [hd, hq]
    norm_num
