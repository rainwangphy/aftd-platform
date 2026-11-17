import AFTD.Prelude

/-!
# quaternion_spinor_matrix

Topic: quantum   Node: 1ef135ca5ed3

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, quaternion reference spinor construction.

The complex two by two matrix associated with four quaternion coordinates.
-/

open scoped Matrix

def quaternion_spinor_matrix (q : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q 0 : ℂ)-Complex.I*(q 3 : ℂ), -(q 2 : ℂ)-Complex.I*(q 1 : ℂ);
     (q 2 : ℂ)-Complex.I*(q 1 : ℂ), (q 0 : ℂ)+Complex.I*(q 3 : ℂ)]
