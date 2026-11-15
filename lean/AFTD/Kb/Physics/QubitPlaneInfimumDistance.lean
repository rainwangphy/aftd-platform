import AFTD.Prelude
import AFTD.Kb.Physics.EmbeddedQubitPlane
import AFTD.Kb.Physics.QubitPlaneDistance

/-!
# qubit_plane_infimum_distance

Topic: quantum_mechanics   Node: 03c7d1cff2fe

Provenance: original. Related work: arXiv:2610.37187

The infimum distance D of a family of Hermitian jump operators J_j to any embedded qubit plane, normalized by W.
-/

/-- The infimum normalized squared distance D over all embedded qubit planes. -/
noncomputable def qubit_plane_infimum_distance {ι : Type*} [Fintype ι] {d : ℕ}
    (J : ι → Matrix (Fin d) (Fin d) ℂ) (W : ℝ) : ℝ :=
  sInf (Set.range (qubit_plane_distance J W))
