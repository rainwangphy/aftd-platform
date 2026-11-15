import AFTD.Prelude
import AFTD.Kb.Physics.EmbeddedQubitPlane

/-!
# qubit_plane_distance

Topic: quantum_mechanics   Node: 318490d929c6

Provenance: original. Related work: arXiv:2610.37187

The normalized squared distance of a family of Hermitian operators J_j to an embedded qubit plane Q, given by (sum_j ||J_j - Proj_E(J_j)||_F^2) / W.
-/

/-- The normalized Hilbert-Schmidt distance sum_j ||J_j - Proj_E(J_j)||_F^2 / W to an embedded qubit plane. -/
noncomputable def qubit_plane_distance {ι : Type*} [Fintype ι] {d : ℕ}
    (J : ι → Matrix (Fin d) (Fin d) ℂ) (W : ℝ) (Q : EmbeddedQubitPlane d) : ℝ :=
  (∑ j, ((Matrix.trace (J j * J j)).re -
    ((Matrix.trace (J j * Q.E₁)).re) ^ 2 -
    ((Matrix.trace (J j * Q.E₂)).re) ^ 2)) / W
