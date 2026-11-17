import AFTD.Prelude
import AFTD.Kb.Tcs.QuaternionSpinorMatrix

/-!
# quaternion_spinor_odd

Topic: quantum   Node: adb006927a59

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, quaternion reference spinor construction.

Quaternion spinor matrices are odd under negation of the quaternion.
-/

theorem quaternion_spinor_odd (q : Fin 4 → ℝ) :
    quaternion_spinor_matrix (-q) = -quaternion_spinor_matrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternion_spinor_matrix] <;> ring
