import AFTD.Prelude
import AFTD.Kb.Tcs.GaussBlochA
import AFTD.Kb.Tcs.GaussBlochB
import AFTD.Kb.Tcs.GaussCorr

/-!
# gaussInvariant

Topic: quantum   Node: 7ae108b1f1b8

Provenance: helper lemma. step towards three_qubit_gaussian_witness_not_locally_real

The local-unitary invariant: determinant of the 3x3 real matrix with rows a, A·b, A·Aᵀ·a.
-/

/-- Local-unitary invariant det[a, A b, A Aᵀ a] built from the Bloch vectors and correlation matrix. -/
noncomputable def gaussInvariant (ψ : EuclideanSpace ℂ (Fin 3 → Fin 2)) : ℝ := let a := gaussBlochA ψ
  let b := gaussBlochB ψ
  let A := gaussCorr ψ
  Matrix.det (Matrix.of ![a, A.mulVec b, A.mulVec (A.transpose.mulVec a)])
