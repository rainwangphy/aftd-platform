import AFTD.Prelude

/-!
# quaternion_bloch_rotation

Topic: quantum   Node: bd09e878a1c1

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, quaternion-to-rotation parametrization.

The homogeneous real 3 by 3 rotation matrix associated with four quaternion coordinates.
-/

open scoped Matrix

def quaternion_bloch_rotation (q : Fin 4 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q 0^2+q 1^2-q 2^2-q 3^2, 2*(q 1*q 2-q 0*q 3), 2*(q 1*q 3+q 0*q 2);
     2*(q 1*q 2+q 0*q 3), q 0^2-q 1^2+q 2^2-q 3^2, 2*(q 2*q 3-q 0*q 1);
     2*(q 1*q 3-q 0*q 2), 2*(q 2*q 3+q 0*q 1), q 0^2-q 1^2-q 2^2+q 3^2]
