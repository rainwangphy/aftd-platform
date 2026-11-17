import AFTD.Prelude
import AFTD.Kb.Tcs.QuaternionBlochRotation

/-!
# quaternion_bloch_rotation_neg

Topic: quantum   Node: b1888756e81e

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, quaternion-to-rotation parametrization.

The homogeneous quaternion rotation matrix is invariant under negation of all four quaternion coordinates.
-/

theorem quaternion_bloch_rotation_neg (q : Fin 4 → ℝ) :
    quaternion_bloch_rotation (-q) = quaternion_bloch_rotation q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternion_bloch_rotation, Matrix.cons_val_two] <;> ring
